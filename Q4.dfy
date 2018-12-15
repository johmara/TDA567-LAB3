Question 4: Factorial

method ComputeFact(n : nat) returns (res : nat)
  requires n > 0;
  ensures res == fact(n);
 {
  res := 1;
  var i := 2;
  while (i <= n) 
  {
    res := res * i;
    i := i + 1;
  }
 }
 
 The variables are natural numbers. You are supposed to prove that the program is correct with respect to a recursive definition 
  of the factorial function, defined mathematically as:
  
  fact(1) = 1
  fact(m) = m * fact(m - 1)

 
 
 1.Complete the specification so that Dafny is able to prove ComputeFact correct.
 2.Prove correctness of the loop using the checklist for proving loops correct from the lecture notes. See also Chapter 11 of [Gries].
