//Question 3: Correct program AND missing specs!
/*
method Q3(n0 : int, m0 : int) returns (res : int)
  
{
  var n, m : int;
  res := 0;
  if (n0 >= 0) 
       {n,m := n0, m0;} 
  else 
       {n,m := -n0, -m0;}
  while (0 < n) 
  { 
    res := res + m; 
    n := n - 1; 
  }
}

Why can't we use the inputs directly? (n0, m0)

Because we are not using "modified-clause"

What IS the purpose of method? In other words, what should the specification (postcondition(s)) of the program be?

The purpose is multiplication between two int-values. That it ensures that result of the method is the two inputs multiplied
to each other. With the following input values the method behaved as a multiplying function:
   n,m
   0,0  res = 0
   1,1	res = 1
  -1,1 	res = -1
  1,-1 	res = -1
 -1,-1	res = 1
 
(You can of course always give a silly specification for which the program is correct, but this will not be considered a correct specification.)
Prove by hand that the program is correct with respect to your specification. Follow the steps in the "checklist" for proving loops correct from the lecture notes. See also Chapter 11 of [Gries].

[Hint] If you successfully figure out the method's purpose, try to include additional specification so that you can demonstrate the correctness of this program against standard library function.
*/
method Q3(n0 : int, m0 : int) returns (res : int)
ensures res == n0*m0;
{
  var n, m : int;
  res := 0;
  if (n0 >= 0) 
       {n,m := n0, m0;} 
  else 
       {n, m:= -n0, -m0;}
       
  while (0 < n) 
  invariant m0*n0 = res + m*n;  
  invariant n >= 0;
  decreases n;
  { 
    res := res + m; 
    n := n - 1; 
  }
}
/*
Verification
--------------------------------------------------------------------------------------
method Q3(n0 : int, m0 : int) returns (res : int)
Q 
{
  var n, m : int;
  S1
  while (0 < n) 
  I
  decreases n;
  { S2 }
}


ensures R: res == n0*m0
statement S1: res:= 0; if (n0 >=0) then (n,m := n0,m0) else (n,m := -n0,-m0)
statement S2: res= res + m, n := n - 1; 
invariant I: m0*n0 = res + m*n
While guard B: 0 < n
Q = {}


Q -> wp(S1;S2,R) 
Sequential Rule:

wp(S1,wp(S2,R))

While-loop, 
-------------------------------------------------------
wp(while B I D S, R)

I
&& (B && I ==> wp(S,I))
&& (!B && I ==> R)
=
m0*n0 = res + m*n
&& ( 0 < n && m0*n0 = res + m*n ==> wp (S,I))
&& (0 >=n && m0*n0 = res + m*n ==> res == n0*m0)

	wp(S2,I) 
	=
	wp(res= res + m; n := n - 1,  m0*n0 = res + m*n)

		Assignment rule
   		wp(res= res + m, wp(n := n - 1,  m0*n0 = res + m*n))
		-> wp(res= res + m, m0*n0 = res + m*(n - 1)) == m0*n0 = res + m + m*(n - 1)
		-> wp(m0*n0 = res + m + m*n - m) == m0*n0 = res + m*n 

1. m0*n0 = res + m*n
2. && ( 0 < n && m0*n0 = res + m*n ==> m0*n0 = res + m*n
3. && (0 >=n && m0*n0 = res + m*n ==> res == n0*m0)

1 & 2 True if invariant is true
3. if 0 >=n is true, (0 >=n && (m0*n0 = res + m*n ==> res == n0*m0))
   -> (m0*n0 = res + m*n ==> res == n0*m0) = m*n = 0
   -> (0 >=n && m*n = 0)

wp(S2,R) = m0*n0 = res + m*n && ( 0 >= n ==> m*n = 0)

----------------------------------------------------------

Full program with S2 solved
----------------------------------------------------------
wp(S1,wp(S2,R))
=
wp(S1,m0*n0 = res + m*n && ( 0 >= n ==> m*n = 0))

Conditional Rule:
	wp(res:= 0, (n0 > 0) ==>  wp(n,m :=  n0, m0, m0*n0 = res + m*n && ( 0 >= n ==> m*n = 0)) &&
		    (n0 <= 0 ==>  wp(n,m := -n0,-m0, m0*n0 = res + m*n && ( 0 >= n ==> m*n = 0))
Assignment Rule:
	wp((n0 > 0) ==>  wp(n,m :=  n0, m0, m0*n0 = 0 + m*n && ( 0 >= n ==> m*n = 0)) &&
	   (n0 <= 0 ==>  wp(n,m := -n0,-m0, m0*n0 = 0 + m*n && ( 0 >= n ==> m*n = 0))
     -> Simplify if
	  wp((n0 > 0) ==>  wp(m0*n0 = 0 + m0*n0 && ( 0 >= n0 ==> m0*n0 = 0)
     ->   wp((n0 >= 0) ==>  wp( 0 >= n0 ==> m0*n0 = 0)
     -> Simplify else
	  wp((n0 <= 0) ==>  wp(m0*n0 = 0 + -m0*-n0 && ( 0 >= -n0 ==> -m0*-n0 = 0))
     ->   wp((n0 <= 0) ==>  wp( 0 >= -n0 ==> -m0*-n0 = 0))

         wp((n0 >= 0) ==> ( 0 >= n0 ==> m0*n0 = 0) && 
         (n0 <= 0) ==> ( 0 >= -n0 ==> -m0*-n0 = 0))

     ->  wp((n0 == 0) ==> m0*n0 = 0) && 
         (n0 == 0) ==> -m0*-n0 = 0))

     ->  wp((true) && (true))


Decreasing proof (I ==> D >=0)
----------------------------------------------------------
I && B -> n>=0

Simplify
I && 0 < n -> n >=0
-> I && (0 < n) -> 0 < n

Trivial True!

N decreasing proof (B && I ==> wp (tmp := D; S, D < tmp))
----------------------------------------------------------

B && I ==> wp (tmp := n; res:= res + m; n:=n-1, n < tmp)

Sequential:
B && I ==> wp (tmp := n, wp(res:= res + m,wp(n:=n-1, n < tmp)))

Assignment:
wp(tmp := n, wp(res:= res + m,wp(n:=n-1, n < tmp)))
-> wp(tmp := n, wp(res:= res + m, n-1 < tmp)))
-> wp(tmp := n, n-1 < tmp))
-> wp(n-1 < n)
B && I ==> n-1 < n

Trivial True!
	
*/
