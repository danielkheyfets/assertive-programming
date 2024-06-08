
// Daniel Kheyfets 20799333. Liel Keren 31574222

datatype Tree = Empty | Node(int,Tree,Tree)

method Main() {
	var tree := BuildBST([-2,8,3,9,2,-7,0]);
	PrintTreeNumbersInorder(tree);
}

method PrintTreeNumbersInorder(t: Tree)
{
	match t {
		case Empty =>
		case Node(n, l, r) =>
			PrintTreeNumbersInorder(l);
			print n;
			print "\n";
			PrintTreeNumbersInorder(r);
	}
}

function NumbersInTree(t: Tree): set<int>
{
	NumbersInSequence(Inorder(t))
}

function NumbersInSequence(q: seq<int>): set<int>
{
	set x | x in q
}

predicate BST(t: Tree)
{
	Ascending(Inorder(t))
}

function Inorder(t: Tree): seq<int>
{
	match t {
		case Empty => []
		case Node(n',nt1,nt2) => Inorder(nt1)+[n']+Inorder(nt2)
	}
}

predicate Ascending(q: seq<int>)
{
	forall i,j :: 0 <= i < j < |q| ==> q[i] < q[j]
}

predicate NoDuplicates(q: seq<int>) { forall i,j :: 0 <= i < j < |q| ==> q[i] != q[j] }

/*
	Goal: Implement correctly, clearly. No need to document the proof obligations.
*/
method BuildBST(q: seq<int>) returns (t: Tree)
	requires NoDuplicates(q)
	ensures BST(t) && NumbersInTree(t) == NumbersInSequence(q)
{
        var i := 0;
        t := Empty;
        while( i < |q|)
            invariant BST(t)
            invariant 0 <= i <= |q|
            invariant NumbersInSequence(q[i..]) + NumbersInTree(t) == NumbersInSequence(q)
            invariant forall k :: i<= k < |q| ==> q[k] !in NumbersInTree(t);

        {
            assert NumbersInSequence(q[i..]) + NumbersInTree(t) == NumbersInSequence(q) == NumbersInSequence(Inorder(t) +q[i..]);
            assert NoDuplicates(q);
            assert NoDuplicates(q);
            assert forall k :: i<= k < |q| ==> q[k] !in NumbersInTree(t);
            assert q[i] !in NumbersInTree(t);
            t:= InsertBST(t,q[i]);
            i:=i+1;
        }
    }
/*
	Goal: Implement correctly, efficiently, clearly, documenting the proof obligations
	as we've learned, with assertions and a lemma for each proof goal
*/
method InsertBST(t0: Tree, x: int) returns (t: Tree)
	requires BST(t0) && x !in NumbersInTree(t0)
	ensures BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x}
 {
       assert BST(t0) && x !in NumbersInTree(t0);
       match t0 {
        case Empty => 
            assert BST(t0) && x !in NumbersInTree(t0);
            assert BST(Empty) && x !in NumbersInTree(Empty);
             L_3(x, t0);
            // ==>
            assert BST(Node(x, Empty, Empty)) && NumbersInTree(Node(x, Empty, Empty)) == NumbersInTree(t0)+{x};
            t := Node(x, Empty, Empty);
            assert BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x};


        case Node(n',left,right) =>
            assert BST(t0) && x !in NumbersInTree(t0);
            assert t0 == Node(n',left,right);
            LemmaBinarySearchSubtree(n',left,right);
            //=>
            assert BST(left);
            assert BST(right);
            assert right < t0;
            assert left < t0;

            if( x > n' ){
                assert BST(t0) && x !in NumbersInTree(t0);
                assert t0 == Node(n',left,right);
                assert x > n';
                assert BST(left);
                assert BST(right);
                assert x !in NumbersInTree(t0);
                //=>
                assert BST(right) && x !in NumbersInTree(right); // x not int  t0 so it not in right to.

                var newRight := InsertBST(right, x); //recursion call
                //==>
                assert BST(newRight) && NumbersInTree(newRight) == NumbersInTree(right)+{x};
                // ==>
                assert x !in NumbersInTree(t0);
                assert x in Inorder(newRight);
                assert t0 == Node(n',left,right);
                assert NumbersInTree(newRight) == NumbersInTree(right)+{x};

                L_NUMBERS_IN_TREE_RIGHT(x,t0,n',left,right,newRight);
                //==>
                assert NumbersInTree(Node(n', left, newRight)) == NumbersInTree(t0)+{x};
                
                assert BST(t0) && x !in NumbersInTree(t0);
                assert t0 == Node(n',left,right);
                assert x > n';
                assert BST(left);
                assert BST(right);
                assert BST(newRight);
                assert x in Inorder(newRight);
                assert NumbersInTree(newRight) == NumbersInTree(right)+{x};
                L_1(x,t0,n',left,right,newRight);
                //==>
                assert(BST(Node(n', left, newRight)));

                //==>
                assert BST( Node(n', left, newRight)) && NumbersInTree( Node(n', left, newRight)) == NumbersInTree(t0)+{x};

                t:= Node(n', left, newRight);
                assert BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x};

            }
            else{ //x < n'
                assert BST(t0) && x !in NumbersInTree(t0);
                assert t0 == Node(n',left,right);
                assert x < n';
                assert BST(left);
                assert BST(right);
                assert x !in NumbersInTree(t0);
                //=>
                assert BST(left) && x !in NumbersInTree(left);

                var newLeft := InsertBST(left, x);
                //=>
                assert BST(newLeft) && NumbersInTree(newLeft) == NumbersInTree(left)+{x};
                //=>
                assert x !in NumbersInTree(t0);
                assert NumbersInTree(newLeft) == NumbersInTree(left)+{x};
                assert x in Inorder(newLeft);
                assert t0 == Node(n',left,right);
                L_NUMBERS_IN_TREE_LEFT(x,t0,n',left,right,newLeft);
                //==>
                assert NumbersInTree(Node(n', newLeft, right)) == NumbersInTree(t0)+{x};

                assert BST(t0) && x !in NumbersInTree(t0);
                assert t0 == Node(n',left,right);
                assert x < n';
                assert BST(left);
                assert BST(right);
                assert BST(newLeft);
                assert x in Inorder(newLeft);
                assert NumbersInTree(newLeft) == NumbersInTree(left)+{x};
                L_2(x,t0,n',left,right,newLeft);
                //=>
                assert BST(Node(n', newLeft, right));

                //=>
                assert BST(Node(n', newLeft, right)) && NumbersInTree(Node(n', newLeft, right)) == NumbersInTree(t0)+{x};
                t:= Node(n', newLeft, right);
                assert BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x};

            }
       }
       assert BST(t) && NumbersInTree(t) == NumbersInTree(t0)+{x};
    }



lemma L_3(x:int, t0:Tree)
    requires BST(t0) && x !in NumbersInTree(t0);
    requires t0 == Empty
    ensures BST(Node(x, Empty, Empty)) && NumbersInTree(Node(x, Empty, Empty)) == NumbersInTree(t0)+{x}
    {
    assert BST(t0) && x !in NumbersInTree(t0);
    assert t0 == Empty;
    assert BST(t0) && x !in NumbersInTree(t0);
    //=>
    assert NumbersInTree(Node(x, Empty, Empty)) == NumbersInTree(Empty)+{x};
    //=>
    assert NumbersInTree(Node(x, Empty, Empty)) == NumbersInTree(t0)+{x};
    assert BST(Node(x, Empty, Empty));
    assert BST(Node(x, Empty, Empty)) && NumbersInTree(Node(x, Empty, Empty)) == NumbersInTree(t0)+{x}; 
    }

lemma L_1(x:int, t0:Tree,n':int,left:Tree, right:Tree,newRight:Tree)
    requires BST(t0) && x !in NumbersInTree(t0);
    requires t0 == Node(n',left,right);
    requires x > n';
    requires BST(left);
    requires BST(right);
    requires BST(newRight);
    requires x in Inorder(newRight);
    requires NumbersInTree(newRight) == NumbersInTree(right)+{x};
    ensures BST(Node(n', left, newRight))
    {
    assert BST(t0) && x !in NumbersInTree(t0);
    assert t0 == Node(n',left,right);
    assert x > n';
    assert BST(left);
    assert BST(right);
    assert BST(newRight);
    assert x in Inorder(newRight);
    assert NumbersInTree(newRight) == NumbersInTree(right)+{x};
    //=>
    assert Ascending(Inorder(Node(n', left, right)));
    assert t0 == (Node(n', left, right));
    assert Ascending(Inorder(left)) && Ascending(Inorder(right));
    L_THIS_IS_BST(t0, n', left, right);
    assert Ascending([n'] + Inorder(right));
    assert Ascending( Inorder(left) + [n']);
    assert forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n';
    assert forall i:: 0 <= i < |Inorder(right)| ==>  n' < Inorder(right)[i] ;
    //==>
    assert forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n';
    assert forall i:: 0 <= i < |Inorder(right)| ==>  n' < Inorder(right)[i] ;
    assert forall i:: 0 <= i < |Inorder(newRight)| ==>  Inorder(newRight)[i] == x || Inorder(newRight)[i] in NumbersInTree(right) ;
    assert n' < x;
    //=>
    assert forall i:: 0 <= i < |Inorder(newRight)| ==>  n' < Inorder(newRight)[i] ;
    assert forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n';
    assert Inorder(Node(n', left, newRight)) == Inorder(left) + [n'] + Inorder(newRight);

    //=>
    assert forall i,j :: 0 <= i < j < |Inorder(Node(n', left, newRight))| ==> Inorder(Node(n', left, newRight))[i] < Inorder(Node(n', left, newRight))[j];
    //=>
    assert BST(Node(n', left, newRight));
    }

lemma L_2(x:int, t0:Tree,n':int,left:Tree, right:Tree,newLeft:Tree)
    requires BST(t0) && x !in NumbersInTree(t0);
    requires t0 == Node(n',left,right);
    requires x < n';
    requires BST(left);
    requires BST(right);
    requires BST(newLeft);
    requires x in Inorder(newLeft);
    requires NumbersInTree(newLeft) == NumbersInTree(left)+{x};
    ensures BST(Node(n', newLeft, right))
    {
    assert BST(t0) && x !in NumbersInTree(t0);
    assert t0 == Node(n',left,right);
    assert x < n';
    assert BST(left);
    assert BST(right);
    assert BST(newLeft);
    assert x in Inorder(newLeft);
    assert NumbersInTree(newLeft) == NumbersInTree(left)+{x};
    //=>
    assert Ascending(Inorder(Node(n', left, right)));
    assert t0 == (Node(n', left, right));
    assert Ascending(Inorder(left)) && Ascending(Inorder(right));
    L_THIS_IS_BST(t0, n', left, right);
    assert Ascending([n'] + Inorder(right));
    assert Ascending( Inorder(left) + [n']);
    assert forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n';
    assert forall i:: 0 <= i < |Inorder(right)| ==>  n' < Inorder(right)[i] ;
    //==>
    assert forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n';
    assert forall i:: 0 <= i < |Inorder(right)| ==>  n' < Inorder(right)[i] ;
    assert forall i:: 0 <= i < |Inorder(newLeft)| ==>  Inorder(newLeft)[i] == x || Inorder(newLeft)[i] in NumbersInTree(left) ;
    assert n' > x;
    //==>
    assert forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n';
    assert forall i:: 0 <= i < |Inorder(newLeft)| ==>  n' > Inorder(newLeft)[i] ;
    assert Inorder(Node(n', newLeft, right)) == Inorder(newLeft) + [n'] + Inorder(right);
    //=>
    assert forall i,j :: 0 <= i < j < |Inorder(Node(n', newLeft, right))| ==> Inorder(Node(n',newLeft, right))[i] < Inorder(Node(n', newLeft, right))[j];
    //=>
    assert BST(Node(n', newLeft, right));
    }

lemma L_NUMBERS_IN_TREE_RIGHT(x:int, t0:Tree,n':int,left:Tree, right:Tree,newRight:Tree)
	requires x !in NumbersInTree(t0)
    requires x in Inorder(newRight)
    requires t0 == Node(n',left,right)
    requires NumbersInTree(newRight) == NumbersInTree(right)+{x};
	ensures NumbersInTree(Node(n', left, newRight)) == NumbersInTree(t0)+{x};
{
       	assert x !in NumbersInTree(t0);
        //=>
        assert x !in NumbersInTree(left);
        assert x !in NumbersInTree(right);
        assert  NumbersInTree(newRight) == NumbersInTree(right)+{x};
        assert x in Inorder(newRight);
        //=>
        assert x in NumbersInTree(Node(n', left, newRight)) ;
        //=>
        assert NumbersInTree(Node(n', left, newRight)) == NumbersInTree(t0)+{x};
}

lemma L_NUMBERS_IN_TREE_LEFT(x:int, t0:Tree,n':int,left:Tree, right:Tree,newLeft:Tree)
	requires x !in NumbersInTree(t0)
    requires x in Inorder(newLeft)
    requires t0 == Node(n',left,right)
    requires NumbersInTree(newLeft) == NumbersInTree(left)+{x};
	ensures NumbersInTree(Node(n', newLeft, right)) == NumbersInTree(t0)+{x};
{
    	assert x !in NumbersInTree(t0);
        //=>
        assert x !in NumbersInTree(left);
        assert x !in NumbersInTree(right);
        assert  NumbersInTree(newLeft) == NumbersInTree(left)+{x};
        assert x in Inorder(newLeft);
        //=>
        assert x in NumbersInTree(Node(n', newLeft, right)) ;
        //=>
        assert NumbersInTree(Node(n', newLeft, right)) == NumbersInTree(t0)+{x};
}

lemma L_THIS_IS_BST(t0: Tree, n': int, left: Tree ,right: Tree)
    requires Ascending(Inorder(Node(n', left, right)))
    requires t0 == (Node(n', left, right))
    requires Ascending(Inorder(left)) && Ascending(Inorder(right));
    ensures Ascending([n'] + Inorder(right))
    ensures Ascending( Inorder(left) + [n']);
    ensures forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n'
    ensures forall i:: 0 <= i < |Inorder(right)| ==>  n' < Inorder(right)[i] ;
    {
    assert Ascending(Inorder(Node(n', left, right)));
    assert Ascending(Inorder(left)) && Ascending(Inorder(right));
    ghost var right_seq := Inorder(right);
    ghost var left_seq := Inorder(left);
    ghost var t0_seq := left_seq + [n'] + right_seq;
    assert Ascending(t0_seq);
    assert Ascending(left_seq) && Ascending(right_seq);

    assert |left_seq| <= |t0_seq| - |[n'] + right_seq|;
    assert [n'] + right_seq == t0_seq[|left_seq|..|left_seq|+|[n'] + right_seq|];
    LemmaAscendingSubsequence(t0_seq, [n'] + right_seq, |left_seq|);
    //=>
    assert Ascending([n'] + right_seq);
    
    
    assert 0 <= |t0_seq| - |left_seq + [n']|;
    assert left_seq + [n'] == t0_seq[0..0+|left_seq + [n']|];
    LemmaAscendingSubsequence(t0_seq, left_seq + [n'], 0);
    //=>
    assert Ascending( left_seq + [n']);

    assert Ascending([n'] + right_seq);
    assert Ascending(left_seq + [n']);
    assert (left_seq + [n'])[|left_seq + [n']|-1] == ([n'] + right_seq)[0];
    assert n' !in NumbersInTree(left);
    assert n' !in NumbersInTree(right);
    //=>
    assert forall i:: 0 <= i < |Inorder(left)| ==> Inorder(left)[i] < n';
    assert forall i:: 0 <= i < |Inorder(right)| ==>  n' < Inorder(right)[i] ;
    //=>
    assert Ascending([n'] + Inorder(right));
    assert Ascending( Inorder(left) + [n']);
    }

lemma	LemmaBinarySearchSubtree(n: int, left: Tree, right: Tree)
	requires BST(Node(n, left, right))
	ensures BST(left) && BST(right)
{
	assert Ascending(Inorder(Node(n, left, right)));
	var qleft, qright := Inorder(left), Inorder(right);
	var q := qleft+[n]+qright;
	assert q == Inorder(Node(n, left, right));
	assert Ascending(qleft+[n]+qright);
	assert Ascending(qleft) by { LemmaAscendingSubsequence(q, qleft, 0); }
	assert Ascending(qright) by { LemmaAscendingSubsequence(q, qright, |qleft|+1); }
}

lemma LemmaAscendingSubsequence(q1: seq<int>, q2: seq<int>, i: nat)
	requires i <= |q1|-|q2| && q2 == q1[i..i+|q2|]
	requires Ascending(q1)
	ensures Ascending(q2)
{}

lemma LemmaAscendingSubsequence2(q1: seq<int>, q2: seq<int>, i: nat)
	requires Ascending(q2)
	requires Ascending(q1)
    requires |q1| >0 && |q2| > 0
    requires q1[|q1|-1] == q2[0]
	ensures Ascending(q1 + q2[1..])
{}

