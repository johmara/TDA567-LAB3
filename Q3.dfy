//Question 3: Correct program AND missing specs!

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
  invariant n0 >= 0 ==> (res == m*(n0-n) && m == m0);  
  invariant n0 < 0 ==> (res == m*(-n0-n) && m == -m0); 
  invariant n >= 0;
  decreases n;
  { 
    res := res + m; 
    n := n - 1; 
  }
}

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

ensures Q: res == n0*m0
statement S1: res:= 0; if (n0 >=0) then (n,m := n0,m0) else (n,m := -n0,-m0)
statement S2: res= res + m; 
invariant I: n0 >= 0 ==> (res == m*( n0-n) && m ==  m0) &&
			 n0 <  0 ==> (res == m*(-n0-n) && m == -m0) &&
			 n >= 0;
wp(S1; while (0 < n) do S2)

Invariant Holds entering the Loop:
-------------------------------------------------------------
Sequential:
	wp(S1, I) = wp(res:= 0; if (n0 >=0) then (n,m := n0,m0) else (n,m := -n0,-m0), I)
	
Conditional:
	wp(res:= 0, (n0 >=0) ==>(n,m := n0,m0) &&
				(!(n0 >= 0) ==> (n,m := -n0,-m0), I)
				
Assignment: Inner assignment first
	wp(res:= 0, 
		(n0 >=0) ==> (n0 >= 0 ==> (res == m*( n0-n) && m ==  m0) &&
		n0 <  0 ==> (res == m*(-n0-n) && m == -m0) &&
		n >= 0)
	&&
		(!(n0 >= 0) ==> (n0 >= 0 ==> (res == m*( n0-n) && m ==  m0) &&
		 n0 <  0 ==> (res == m*(-n0-n) && m == -m0) &&
		-n0 >= 0)
	(res = 0) =>
		(n0 >=0) ==> (n0 >= 0 ==> (0 == 0 && m ==  m0) &&
		n0 <  0 ==> (0 == 0 && m == -m0) &&
		n >= 0)
	&&
		(!(n0 >= 0) ==> (n0 >= 0 ==> (0 == 0) && m ==  m0) &&
		n0 <  0 ==> (0 == 0) && m == -m0) &&
		-n0 >= 0)
	 Which evaluates to True,

Invariant Holds during loop:	
-------------------------------------------------------------
	(B && I) ==> wp (S2,I) = (0 < n && I) ==> wp(res:= res + m; n:= n - 1, I)
	
Sequential:
	(I && 0 < n) ==> wp(res := res + m, wp(n := n - 1, I))
	
Assignment: Inner assignment first (n := n - 1)
	(0 < n && I) ==> wp(res := res + m,
		n0 >= 0 ==> (res == m * ( n0 - (n - 1)) && m ==  m0) &&
		n0 <  0 ==> (res == m * (-n0 - (n - 1)) && m == -m0) &&
		n - 1 >= 0)

Assignment: Res assignment (res := res + m)
	(0 < n && I) ==>
		n0 >= 0 ==> (res + m == m * ( n0 - (n - 1)) && m ==  m0) &&
		n0 <  0 ==> (res + m == m * (-n0 - (n - 1)) && m == -m0) &&
		n - 1 >= 0);
	=  
		n0 >= 0 ==> (res == m * ( n0 - n ) && m ==  m0) &&
		n0 <  0 ==> (res == m * (-n0 - n ) && m == -m0) &&
		n - 1 >= 0);
	
		n0 >= 0 ==> (res == m * ( n0 - n ) && m ==  m0) && // Invariant statement
		n0 <  0 ==> (res == m * (-n0 - n ) && m == -m0) && // Invariant statement
		n - 1 >= 0 //To do new iteration n must be >= 1'
		
		==> n0 >= 0 ==> (true && true) && // Invariant statement
		    n0 <  0 ==> (true && true) && // Invariant statement
		    n - 1 >= 0 //To do new iteration n must be >= 1 true
			
---------------------------------------------------------------			
Postcondition Holds after loop: (Q)
	(B && I) ==> (Q)
	(0 >= n && I) ==> (res == n0 * m0)
	
	=
	
	(n0 >= 0 ==> (res == m * ( n0 - n) && m ==  m0)) &&
        (n0 <  0 ==> (res == m * (-n0 - n) && m == -m0)) &&
        n >= 0 && 0 >= n  ==> (res = n0 * m0)
	  
        {n >= 0 && 0 >= n // simplify n==0}
	=
	
	(n0 >= 0 ==> (res == m * ( n0 - n) && m ==  m0)) &&
        (n0 <  0 ==> (res == m * (-n0 - n) && m == -m0)) &&
        n == 0  ==> (res = n0 * m0)
		
	= 
	
	1.(n0 >= 0 ==> (res == m * ( n0 ) && m ==  m0)) && 
        2.(n0 <  0 ==> (res == m * (-n0 ) && m == -m0)) && 
 	   n == 0 ==> (res = n0 * m0)
	
	By fullfilling n == 0 ->
	1. res == m0*n0 since m == m0
	2. res == m0*n0 since m == -m0 => res == -m0*-n0 == m0*n0
----------------------------------------------------------------
Variant hold until end of loop
	
	(B && I) ==> n > 0
	=
	(0 < n && I) ==> n > 0
	
	n < 0 == n > 0 
	
	Which is Trivially True
	
------------------------------------------------------------------
Variant decreases each iteration

	(B && I) ==> wp(tmp:=n; S , n < tmp)
	=
	(0 < n && I) ==> wp(tmp:= n ; res:= res + m; n:= n - 1, n < tmp)
	
	<==> {sequential x4}
	
	(0 < n && I) ==> wp(tmp:= n, wp(res:= res + m, wp( n:= n - 1, wp({}, n < tmp))))
	
	<==> {empty program}
	
	(0 < n && I) ==> wp(tmp:= n, wp(res:= res + m, wp( n:= n - 1, n < tmp))))

	<==> {assignment}
	
	(0 < n && I) ==> wp(tmp:= n, wp(res:= res + m, n - 1 < tmp))
	
	<==> {assignment}
	
	(0 < n && I) ==> wp(tmp:= n, n - 1 < tmp))
	
	<==> {assignment}
	
	(0 < n && I) ==> n - 1 < n0
	
	Which is Trivially TRUE
