/*
// Daniel Kheyfets 20799333. Liel Keren 31574222
// we use rabin karp algorithm here the Average performance O(|text|+|patern|) but the worst case O(|text||patren|) the space complexity O(|text|) because we need build a new set every iteration
//our sourse for this algorithm https://www.geeksforgeeks.org/rabin-karp-algorithm-for-pattern-searching
The Rabin-Karp algorithm is best used when searching for a relatively small pattern within a large text, such as searching for a word in a document or a DNA sequence in a genome. It is also useful when multiple patterns need to be searched for simultaneously.
The algorithm is particularly efficient when the pattern being searched for has a low entropy, which means that it has few distinct characters or is highly repetitive. In such cases, the hash function used in the algorithm can generate hash values with a high collision rate, which reduces the number of character comparisons needed during pattern matching.
*/

/*
	Goal: implement correctly, efficiently, clearly; no need to document the proof obligations

	Important Notes:
	
	1) the type "string" in Dafny is a syntactic sugar for a sequence of characters ("seq<char>")
	2) the text is expected to be significantly longer than the pattern
	3) please state the time and space complexities of your algorithm
	4) up to 50% of the grade could be dedicated to complexity of the algorithm / efficiency of the implementation
	   [meaning: a naive O(|text|*|pattern|)-time loop making |text|-|pattern| sequence comparisons is highly discouraged]
	5) if you're implementing some known/published algorithm, please state the sources clearly, including all relevant links
	6) we haven't learned it, but curiously, Dafny supports "set comprehension",
	   such that this method could be implemented with a single assignment:
	   
	   "offsets := set i | 0 <= i <= |text|-|pattern| && text[i..i+|pattern|] == pattern;"
	   
	   naturally, any implementation making such magical shortcuts is not accaptable

	In case you are making a concious choice between alternative algorithms, where the superiority of the complexity may depend
	on the frequency of the occurrences or other properties of the input, you're encouraged to justify this choice in writing;
	questions regarding the preference between known algorithms or potential competing aspects of complexity will not be answered;
	the floor is yours to make a choice and justify it; enjoy!
*/
method FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
	ensures forall i :: i in offsets ==> i + |pattern| <= |text|
	ensures forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
{
        var M := |pattern|;
        var N := |text|;
        if( M <= N ){
        var i := 0; 
        var j := 0;
        var p := 0; // hash value for pattern
        var t := 0; // hash value for txt
        offsets := {};
        
        while( i < M )
            invariant forall k :: k in offsets ==> k + |pattern| <= |text|
            invariant 0 <= i <= M
            invariant p == HashSumDown(pattern[..i])
            invariant t == HashSumDown(text[..i])

        {
            assert pattern[..i+1] == pattern[..i]+[pattern[i]]; 
            assert text[..i+1] == text[..i]+[text[i]]; 

            p := p + (pattern[i]) as int;
            t := t + (text[i]) as int;
            i := i + 1;
        }
        assert pattern[..i] == pattern;
        i:= 0;

        while(i <= N-M)
            invariant |text| >= i + |pattern| -1
            invariant forall i :: i in offsets ==> i + |pattern| <= |text|
            invariant forall k :: 0 <= k < i  ==> (text[k..k+|pattern|] == pattern <==> k in offsets)
            invariant 0 <= i 
            invariant p == HashSumDown(pattern)
            invariant p != t && i + |pattern| <= |text| ==> text[i..i + |pattern|] != pattern
            invariant forall j:: i <= j ==> j !in offsets
            invariant forall j:: 0 <=j < i ==> j !in offsets ==>  text[j..j + |pattern|] != pattern
            invariant i + |pattern| < |text| ==> t == HashSumDown(text[i..i + |pattern|])
        
            {
                
            if(p == t)
            { 
                assert i<=N-M;
                assert i<=|text| - |pattern|;

                var isEq :=  isEq(text, pattern,i);
                if(isEq)
                {
                    offsets := offsets +  {i};
                    assert forall k :: 0 <= k < i +1  ==> (text[k..k+|pattern|] == pattern <==> k in offsets);

                }
                else{
                    assert isEq ==false;
                    assert !isEq ==> text[i.. i + |pattern|] != pattern;
                    assert text[i.. i + |pattern|] != pattern;
                    assert i in offsets ==> text[i.. i + |pattern|] == pattern; 
                    assert forall k :: 0 <= k <= i  ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
                    assert forall k :: 0 <= k < i +1  ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
                    assert i + |pattern| < |text| ==> t == HashSumDown(text[i..i + |pattern|]);

                }
            }else{
               assert 0<=i<= |text| - |pattern|==>i in offsets ==> text[i.. i + |pattern|] == pattern;
                    assert  i + |pattern| < |text| ==> t == HashSumDown(text[i..i + |pattern|]);
                    assert p!=t;
                    assert i !in offsets;
                    assert text[i..i+|pattern|] != pattern;
                    assert forall k :: 0 <= k < i +1  ==> (text[k..k+|pattern|] == pattern <==> k in offsets);

            }

               assert 0<=i<= |text| - |pattern|==>i in offsets ==> text[i.. i + |pattern|] == pattern;

                        assert i + |pattern| < |text| ==> t == HashSumDown(text[i..i + |pattern|]);

            if( i < N - M)
            {
                assert t == HashSumDown(text[i..i + |pattern|]);
                var oldt := t;
                t := t - (text[i] as int) + text[i + M] as int;
                L_1(text,pattern,oldt,t,i+1);
                assert  t == HashSumDown(text[i+1..i+1 + |pattern|]);

               assert 0<=i<= |text| - |pattern|==>i in offsets ==> text[i.. i + |pattern|] == pattern;

            }
            assert forall k :: 0 <= k < i +1  ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
                        assert i + |pattern| < |text| ==> t == HashSumDown(text[i+1..i+1 + |pattern|]);
               

            i := i +1;
            assert forall k :: 0 <= k < i  ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
                        assert i + |pattern| < |text| ==> t == HashSumDown(text[i..i + |pattern|]);


            }
            assert forall i :: i in offsets ==> i + |pattern| <= |text|;
            assert forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets);
                        assert i + |pattern| < |text| ==> t == HashSumDown(text[i..i + |pattern|]);

        }
        else{
            offsets := {};
            assert  forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets);
            assert forall i :: i in offsets ==> i + |pattern| <= |text|;

        }
    
    }



    function HashSumDown(q: string): int
	decreases |q|
{
	if q == [] then 0 else (q[|q|-1] as int)+HashSumDown(q[..|q|-1])
}
function HashSumUp(q: string): int
	decreases |q|
{
	if q == [] then 0 else (q[0]as int)+HashSumUp(q[1..])
}


lemma  EquivalentSumDefinitions(q: string)
	ensures HashSumDown(q) == HashSumUp(q)
	decreases |q|
{
	if |q| == 0
	{
		assert q == [];
		assert HashSumDown([]) == 0 == HashSumUp([]);
	}
	else if |q| == 1
	{
		assert q == [q[0]];
		assert HashSumDown(q) == q[0] as int == HashSumUp(q);
	}
	else
	{
		assert |q| >= 2;
		var first:char, mid:seq<char>, last:char := q[0], q[1..|q|-1], q[|q|-1];
		assert q == [first] + mid + [last];
		calc {
			HashSumDown(q);
		== { assert q != [] && q[|q|-1] as int == last as int && q[..|q|-1] == [first] + mid; }
			last as int + HashSumDown([first] + mid);
		== // arithmetic
			HashSumDown([first] + mid) + last as int;
		== { EquivalentSumDefinitions([first] + mid); } // induction hypothesis
			HashSumUp([first] + mid) as int + (last as int);
		== { assert [first] + mid != []; }
			first as int + HashSumUp(mid) + last as int;
		== { EquivalentSumDefinitions(mid); } // induction hypothesis
			first as int + HashSumDown(mid) + last as int;
		==
			first as int + HashSumDown(mid + [last]);
		== { EquivalentSumDefinitions(mid + [last]); } // induction hypothesis
			first as int + HashSumUp(mid + [last]);
		== { assert q != [] && q[0] == first && q[1..] == mid + [last]; }
			HashSumUp(q);
		}
	}
}

predicate isStringEquals(text: string, pattern: string, j:int)
    requires 0 <= j<= |text| - |pattern|

{

    |text[j..j+|pattern|]| == |pattern| && forall i :: 0 <= i < |pattern| ==> pattern[i] == text[j..j+|pattern|][i]
}
method isEq(text: string, pattern: string, i:int) returns (res: bool)
    requires 0 <= i <= |text| - |pattern|
    ensures text[i.. i + |pattern|] == pattern <==> res== true;
{
    
    res :=text[i.. i + |pattern|] == pattern;
}


method L_1(text:string, pattern:string, oldHash: int, newHash:int, i:int)
    requires 0 < i <= |text| - |pattern|
    requires oldHash == HashSumDown(text[i-1..i-1+|pattern|])
    requires newHash == oldHash - text[i-1] as int + text[i-1 +|pattern|] as int
    ensures newHash == HashSumDown(text[i..i+|pattern|])
    {
        calc{
            newHash;
                ==
             oldHash - text[i-1] as int + text[i-1 +|pattern|] as int;
                ==
            HashSumDown(text[i-1..i-1+|pattern|]) - text[i-1] as int + text[i-1 +|pattern|] as int;
                == 
            HashSumDown(text[i-1..i-1+|pattern|]) - HashSumDown([text[i-1] ]) + HashSumDown([text[i-1 +|pattern|]] );

                == {
                    assert text[i-1..i+|pattern|] == text[i-1..i-1+|pattern|] + [text[i-1 +|pattern|]];
                    assert HashSumDown(text[i-1..i+|pattern|]) == HashSumDown(text[i-1..i-1+|pattern|]) + HashSumDown( [text[i-1 +|pattern|]] );
                    assert HashSumDown(text[i-1..i-1+|pattern|]) == HashSumDown(text[i-1..i+|pattern|]) - HashSumDown( [text[i-1 +|pattern|]] );
                    //==>
                    assert text[i-1..i+|pattern|] == [text[i-1]] + text[i..i+|pattern|];
                    assert HashSumUp(text[i-1..i+|pattern|]) == HashSumUp([text[i-1]]) + HashSumUp(text[i..i+|pattern|]);
                    EquivalentSumDefinitions(text[i-1..i+|pattern|]);
                    EquivalentSumDefinitions([text[i-1]]);
                    EquivalentSumDefinitions(text[i..i+|pattern|]);
                    assert HashSumDown(text[i-1..i+|pattern|]) == HashSumDown([text[i-1]]) + HashSumDown(text[i..i+|pattern|]);
                    assert HashSumDown(text[i-1..i+|pattern|]) == HashSumDown([text[i-1]]) +HashSumDown(text[i..i+|pattern|]);
                    assert HashSumDown(text[i-1..i-1+|pattern|]) == HashSumDown(text[i..i+|pattern|]) -HashSumDown( [text[i-1 +|pattern|]] )+  HashSumDown([text[i-1]]) ;
                    assert HashSumDown(text[i-1..i-1+|pattern|]) == HashSumDown(text[i..i+|pattern|]) - text[i-1 +|pattern|] as int +  text[i-1] as int ;}
            HashSumDown(text[i..i+|pattern|]);
        }
    }

method Main() {
	var text, pattern := "Goal: implement correctly, efficiently, clearly; no need to document the proof obligations", " ";
	var res := FindAllOccurrences(text, pattern);
	print "There are ";
	print |res|;
	print " blanks in the string \"" + text + "\"\nThese blank characters are located in the following offsets: ";
	print res;
	assert 5 in res by { assert text[5] == ' ' == pattern[0]; }
	assert 2 !in res by { assert text[2] == 'a' != ' ' == pattern[0]; }
	var char_l: char, char_y: char := 'l', 'y';
	pattern := [char_l, char_y]; // strings in Dafny are sequences of characters
	res := FindAllOccurrences(text, pattern);
	assert 150 !in res;
	assert 23 in res by { assert text[23] == char_l == pattern[0] && text[24] == char_y == pattern[1]; }
	assert 36 in res by {
		assert 36 <= |text| - |pattern|;
		assert text[36..38] == pattern by {
			assert text[36..38] == [text[36], text[37]] == "ly" == [char_l, char_y] == pattern;
		}
	}
	assert 45 in res by { assert text[45] == char_l == pattern[0] && text[46] == char_y == pattern[1]; }
	assert 3 !in res by { assert text[4] == ':' != 'y' == pattern[1]; }
}