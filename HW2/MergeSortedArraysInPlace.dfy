// Daniel Kheyfets 20799333. Liel Keren 31574222
method Main() {
	var a, b := new int[1] [100], new int[3] [4,7,101];
	print "Before merging the following two sorted arrays:\n";
	print a[..];
	print "\n";
	print b[..];
	ghost var AB := multiset(a[..]+b[..]);
	assert Sorted(a[..]) && Sorted(b[..]);
	MergeSortedArraysInPlace(a, b, AB);
	assert multiset(a[..]+b[..]) == AB;
	assert Sorted(a[..]+b[..]);
	print "\nAfter merging:\n";
	print a[..]; // [3,4,5]
	print "\n";
	print b[..]; // [7,8]
}

predicate Sorted(q: seq<int>)
{
	forall i,j :: 0 <= i <= j < |q| ==> q[i] <= q[j]
}

/*
	Goal: Implement iteratively, correctly, efficiently, clearly. No need to document the proof obligations.

	Restriction: Merge the arrays in place, using constant additional space only.
*/
method MergeSortedArraysInPlace(a: array<int>, b: array<int>, ghost AB: multiset<int>)
	requires Sorted(a[..]) && Sorted(b[..])
	requires multiset(a[..]+b[..]) == AB
	requires a != b
	ensures Sorted(a[..]+b[..])
	ensures multiset(a[..]+b[..]) == AB
	modifies a,b
       {
        var m := a.Length;
        var n := b.Length;
        var i := 0;

        if( m > 0 && n > 0){
        
        while(i < m)
            invariant 0 <= i <= m &&  multiset(a[..]+b[..]) == AB &&  Sorted(a[..i]+b[..]) && Sorted(b[..]) && Sorted(a[..])
            invariant forall x,y :: 0<=x < i && 0<= y <n ==> a[x] <= b[y]
            decreases  m-i;
        {
            
            if(a[i] > b[0])
            {
            var temp := a[i];
            a[i] := b[0];
            b[0] :=temp;
            var first := b[0];
            var k := 1;
            ghost var A := multiset(a[..]);
            ghost var B := multiset(b[..]);
            while( k < n &&b[k] < first)

                invariant forall x,y :: 0<=x < i+1 && 0<= y <n ==> a[x] <= b[y]
                invariant multiset(a[..]) == A && Sorted(a[..])
                invariant k <= n  && multiset(b[..]) == B
                invariant forall x,y :: 0 <= x <= y <n && x != k-1 && y != k-1 ==> b[x] <= b[y]
                invariant forall x,y :: 0 <= x <= y < k ==> b[x] <= b[y]
                invariant b[k-1] == first
            {
                first := b[k-1];
                b[k -1] := b[k];
                b[k] := first;
                k := k +1;
            }
        
            }
            else{
            }
            i := i+1;
          
        }
     
        }

    }