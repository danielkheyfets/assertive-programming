/*
DANIEL KHEYFETS 207993833
LIEL KEREN 315794222
*/
/*
	Part A (12%)

	Goal:

	Complete the definition of the program entities below:
	"Guard1", "Inv1", "V1", "Init1", "LoopBody1" and "Lemma1",
	by providing a body, such that the methods ("Init1" and "LoopBody1")
	and the lemma ("Lemma1") will be verifiably correct.

	No need to document the proof obligations.

*/
predicate method Guard1(n: int, a: int)
	requires Inv1(n, a)
    {
        !(a*a <= n)
    }

predicate Inv1(n: int, a: int)
{
       (a+1)*(a+1) > n >=0 && a<=n && a>=0

}

function V1(a: int): int
{
       a + 1

}

method Init1(n: int) returns (a: int)
	requires n >= 0
	ensures Inv1(n, a)
    {
        		a := n;

    }

method LoopBody1(n: int, a0: int) returns (a: int)
	requires Inv1(n, a0) && Guard1(n, a0)
	ensures Inv1(n, a) && 0 <= V1(a) < V1(a0)
    {
                    a:=a0-1;

    }

lemma Lemma1(n: int, a: int)
	requires Inv1(n, a) && !Guard1(n, a)
	ensures a*a <= n && n < (a+1)*(a+1)
    {
        assert Inv1(n, a) && !Guard1(n, a);
        assert a*a <= n && n < (a+1)*(a+1);
    }

method Sqrt_Down_Loop(n: int) returns (a: int)
	requires n >= 0
	ensures a*a <= n && n < (a+1)*(a+1)
{
	a := Init1(n);
	while Guard1(n, a)
		invariant Inv1(n, a)
		decreases V1(a)
	{
		a := LoopBody1(n, a);
	}
	Lemma1(n, a);
}

/*
	Part B (13%)

	Goal:

	Complete the definition of the program entities below:
	"Guard2", "Inv2", "V2", "Init2", "LoopBody2" and "Lemma2",
	by providing a body, such that the methods ("Init2" and "LoopBody2")
	and the lemma ("Lemma2") will be verifiably correct.

	No need to document the proof obligations.

	Restriction:

	Both methods should be implemented with assignment statements only.

*/
function Fib(n: nat): nat
	decreases n
{
	if n == 0 then 0 else if n == 1 then 1 else Fib(n-2) + Fib(n-1)
}

predicate method Guard2(n: nat, i: nat, a: nat, b: nat)
	requires Inv2(n, i, a, b)
    {
        i < n
    }

predicate Inv2(n: nat, i: nat, a: nat, b: nat)
{
      (n==0 && a==0) || (1 <= i <= n && b == Fib(i-1) && a == Fib(i))
}

function V2(n: nat, i: nat, a: nat, b: nat): int
{
    	n-i

}

method Init2(n: nat) returns (i: nat, a: nat, b: nat)
	ensures Inv2(n, i, a, b)
    {
          if(n==0){
            a := 0;
            i :=0;
            b := 0;
        }
        else{
            a, b, i := 1, 0, 1;
        }
    }

method LoopBody2(n: nat, i0: nat, a0: nat, b0: nat) returns (i: nat, a: nat, b: nat)
	requires Inv2(n, i0, a0, b0) && Guard2(n, i0, a0, b0)
	ensures Inv2(n, i, a, b) && 0 <= V2(n, i, a, b) < V2(n, i0, a0, b0)
    {
        a, b := a0 + b0, a0;
		i := i0+1;
    }

lemma Lemma2(n: nat, i: nat, a: nat, b: nat)
	requires Inv2(n, i, a, b) && !Guard2(n, i, a, b)
	ensures a == Fib(n)
    {
        assert Inv2(n, i, a, b) && !Guard2(n, i, a, b);
        assert a == Fib(n);
    }

method ComputeFib2(n: nat) returns (a: nat)
	ensures a == Fib(n)
{
	var i: nat, b: nat;
	i, a, b := Init2(n);
	while Guard2(n, i, a, b)
		invariant Inv2(n, i, a, b)
		decreases V2(n, i, a, b)
	{
		i, a, b := LoopBody2(n, i, a, b);
	}
	Lemma2(n, i, a, b);
}

predicate ValidTimeOfDay(h: int, m: int) { 0 <= h < 24 && 0 <= m < 60 }

/*
	Part C (50%)

	Goal:

	Implement correctly, using a "while" loop, **documenting the proof obligations**
	as we've learned, with assertions and a lemma for each proof goal.

	Restriction:

	The only arithmetic operations allowed in your *code* are addition and subtraction,
	whereas other operations (such as multiplication, division, or modulo) may be used
	in *specification contexts* only (such as assertions and loop invariants).

*/
lemma Lemma_1(h: int, m: int, minutes_since_midnight: int)
    requires m < 60 //pre 1
    requires 0 <= m < 24 * 60; //pre 2
    requires 0 <= h < 24; //pre 3
    requires h *60 + m == minutes_since_midnight; //pre 4

    ensures h *60 + m == minutes_since_midnight; //post 1
    ensures ValidTimeOfDay(h, m); //post 2
    {
        assert ValidTimeOfDay(h, m) by {
            assert 0 <= m < 24 * 60; //pre 2
            assert m < 60;  //by pre 1
            // ==>
            assert 0 <= m < 60;
            assert 0 <= h < 24; //by pre 3
        }

        assert h *60 + m == minutes_since_midnight by {
            assert h *60 + m == minutes_since_midnight; //by pre 4
        }
      
    }


lemma Lemma_2(minutes_since_midnight: int)
    ensures 0 <= minutes_since_midnight < 24*60 //pre 1
    requires 0 <= minutes_since_midnight < 24 * 60;
    requires 0 <= 0 < 24;
    requires 0 *60 + minutes_since_midnight == minutes_since_midnight;
    {
        assert 0 <= minutes_since_midnight < 24 * 60 by{
            assert 0 <= minutes_since_midnight < 24 * 60; //pre 1
        }
        assert 0 <= 0 < 24;

        assert 0 *60 + minutes_since_midnight == minutes_since_midnight by{ 
            assert 0 *60 + minutes_since_midnight == minutes_since_midnight;
            //=>
            assert minutes_since_midnight == minutes_since_midnight;
        }
   
    }


lemma Lemma_3(h: int, m: int, minutes_since_midnight: int)
        requires m >= 60 //pre 1
        requires 0 <= m < 24 * 60 //pre 2
        requires 0 <= h < 24 //pre 3
        requires h *60 + m == minutes_since_midnight //pre 4
        requires 0 <= minutes_since_midnight < 24*60

            
        ensures 0 <= m - 60 < 24 * 60
        ensures 0 <= h + 1 < 24
        ensures (h + 1) *60 + (m-60) == minutes_since_midnight
    {

        assert 0 <= m - 60 < 24 * 60 by {
            assert m >= 60 ;//pre 1
            assert 0 <= m < 24 * 60 ;//pre 2
        }

        assert 0 <= h + 1 < 24 by {
            
            assert h *60 + m == minutes_since_midnight;
            assert 0 <= minutes_since_midnight < 24*60;
            //=> 
            assert h *60 + m <  24*60;
            assert 0 <= h < 24; //pre 3
            assert  m >= 60;
            //=> 
            assert 0 <= h + 1 < 24;
     
        }

        assert (h + 1) *60 + (m-60) == minutes_since_midnight by {
            //trivial we sub 60 from min and ad 1 to hours this is not change the total minutes
        }

    }

method TimeOfDay(minutes_since_midnight: int) returns (h: int, m: int)
	requires 0 <= minutes_since_midnight < 24*60
	ensures h*60+m == minutes_since_midnight
	ensures ValidTimeOfDay(h, m)
{
        assert 0 <= minutes_since_midnight < 24*60;
        Lemma_2(minutes_since_midnight);
        assert 0 <= minutes_since_midnight < 24 * 60;
        assert 0 <= 0 < 24;
        assert 0 *60 + minutes_since_midnight == minutes_since_midnight;
        h := 0;
        m := minutes_since_midnight;
        assert 0 <= m < 24 * 60;
        assert 0 <= h < 24;
        assert h *60 + m == minutes_since_midnight;
        
        while( m >= 60 )
            invariant 0 <= m < 24 * 60
            invariant 0 <= h < 24
            invariant h *60 + m == minutes_since_midnight
            decreases m 
        {
            assert 0 <= minutes_since_midnight < 24*60;
            assert m >= 60;
            assert 0 <= m < 24 * 60;
            assert 0 <= h < 24;
            assert h *60 + m == minutes_since_midnight;

            Lemma_3(h, m, minutes_since_midnight);

            assert 0 <= m - 60 < 24 * 60;
            assert 0 <= h + 1 < 24;
            assert (h + 1) *60 + (m-60) == minutes_since_midnight;
            m := m - 60;
            h := h + 1;
            assert 0 <= m < 24 * 60;
            assert 0 <= h < 24;
            assert h *60 + m == minutes_since_midnight;
        }

        assert m < 24 * 60;
        assert h < 24;
        assert h *60 + m == minutes_since_midnight;
        Lemma_1(h,m,minutes_since_midnight); //=>
        assert h*60+m == minutes_since_midnight;
	    assert ValidTimeOfDay(h, m);
    }
/*
	Part D (25%)

	Goal: Implement correctly. No need to document the proof obligations.

	Restriction:

	Again, the only arithmetic operations allowed in your *code* are addition and subtraction,
	whereas other operations (such as multiplication, division, or modulo) may be used
	in *specification contexts* only (such as assertions and loop invariants).

*/

predicate Inv3(start_h: int, start_m: int, minutes: int, d: int, h: int, m: int){
   start_h*60 + start_m + minutes == d*24*60 + h*60 + m
}



method Init3(start_h: int, start_m: int, minutes: int) returns (d: int, h: int, m: int)
	requires ValidTimeOfDay(start_h, start_m)
	ensures Inv3(start_h, start_m, minutes, d, h, m) && 24 > h >=0
    {
        d:=0;
        h:=start_h;
        m:= minutes + start_m;
    }

method UpdateTime(start_h: int, start_m: int, minutes: int) returns (d: int, h: int, m: int)
	requires ValidTimeOfDay(start_h, start_m)
	ensures ValidTimeOfDay(h, m)
	ensures start_h*60 + start_m + minutes == d*24*60 + h*60 + m
   {
    
        d, h, m := Init3(start_h, start_m, minutes);
        if(m >= 0) {

            while( m >= 60 )
            invariant Inv3(start_h, start_m, minutes, d, h, m)
            decreases m 
            {
                m := m - 60;
                h := h + 1;
            }

            while( h >= 24 )
            invariant Inv3(start_h, start_m, minutes, d, h, m)
            decreases h
            {
                h := h - 24;
                d := d + 1;
            }
        }

        else{
            while( m < 0)
                invariant Inv3(start_h, start_m, minutes, d, h, m) 
                decreases -m 
            {
                
                    m := m +  60;
                    h := h - 1;
           
            }
            while( h < 0 )
                invariant Inv3(start_h, start_m, minutes, d, h, m) 
                decreases -h
                {
                    h := h +  24;
                    d := d - 1;
                }
        }
    }


