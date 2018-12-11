Question 3: Correct program AND missing specs!

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
	invariant	n0 < 0 ==> (res == m*(-n0-n) && m == -m0); 
	invariant	n >= 0;
  decreases n;
  { 
    res := res + m; 
    n := n - 1; 
  }
}
