//Question 4: Factorial

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
 
 /*The variables are natural numbers. You are supposed to prove that the program is correct with respect to a recursive definition
  of the factorial function, defined mathematically as:
  
  fact(1) = 1
  fact(m) = m * fact(m - 1)
 
 1.Complete the specification so that Dafny is able to prove ComputeFact correct.
    method ComputeFact(n : nat) returns (res : nat)
      requires n > 0;
      ensures res == fact(n);
     {
      res := 1;
      var i := 2;
      while (i <= n)
        invariant 2 <= i <= n + 1;
        invariant res == fact(i - 1);
        decreases(n - i);
      {
        res := res * i;
        i := i + 1;
      }
     }

     function fact(n : int) : int
     requires 0 <= n;
     {
         if n == 0 then 1 else n * fact(n - 1)
    }

 2.Prove correctness of the loop using the checklist for proving loops correct from the lecture notes. See also Chapter 11 of [Gries].
    ** Specification

      Q ==> wp(S1; S2, wp(while B I D SS1; SS2, R))

      wp(while B I D S, R)

      Q: n > 0
      R: res == fact(n)

      B: i <= n
      I: 2 <= i <= n + 1 && res == fact(i - 1)
      D: n - i

      S1: res := 1
      S2: i := 2

      SS1: res := res * i
      SS2: i := i + 1



    ** Formula from pdf

      wp(while B I D S, R) =
        I
        && (B && I ==> wp(S, I))
        && (!B && I ==> R)

        && (I ==> D >= 0)
        && (B && I ==>
          wp(tmp := D ; S, tmp > D))



    ** Substitute with actual values

      wp(while i <= n 2 <= i <= n + 1 && res == fact(i - 1) n - i res := res * i; i := i + 1, res == fact(n)) =
        2 <= i <= n + 1 && res == fact(i - 1)
        && (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i; i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1)))
        && (!i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> res == fact(n))

        && (2 <= i <= n + 1 && res == fact(i - 1) ==> n - i >= 0)
        && (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==>
          wp(tmp := n - i ; res := res * i; i := i + 1, tmp > n - i))



    ** Prove invariant preservation during loop

    * Apply Sequential Rule once

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i; i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1)))

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i, wp(i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1))))



    * Apply Assignment Rule twice

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i, wp(i := i + 1, 2 <= i <= n + 1 && res == fact(i - 1))))

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> wp(res := res * i, 2 <= i + 1 <= n + 1 && res == fact(i + 1 - 1)))

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && res * i == fact(i + 1 - 1))



    * Simplify

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && res * i == fact(i))

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && fact(i - 1) * i == fact(i))

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 && true // Trivially true

      (i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1

      (          2 <= i <= n     && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1 // Combine statements

      (          2 <= i <= n     && res == fact(i - 1) ==> 2 <= i + 1 <= n + 1

      (          2 <= i <= n     && res == fact(i - 1) ==> 1 <= i <= n


    * Proof

      Since LHS is a stronger statement than RHS, if LHS is true --> RHS is true.

      If LHS is false, the implication is per definition true.





    ** Prove invariant after loop

      !B && I ==> R

    * Substitute with actual values

      !B && I ==> R

      !(i <= n) && 2 <= i <= n + 1 && res == fact(i - 1) ==> res == fact(n)

    * Simplify

      !(i <= n) && 2 <= i <= n + 1 && res == fact(i - 1) ==> res == fact(n) -->

      (i > n)   && 2 <= i <= n + 1 && res == fact(i - 1) ==> res == fact(n)

      (i > n)   && 2 <= i <= n + 1 && res == fact(i - 1) ==> fact(i - 1) == fact(n)

    * Proof

      The conditions for LHS to evaluate true guarantees that RHS evalutes true

      This is because the condition for RHS to evaluate false is n != i + 1.

      If RHS evaluates false, either of the first two expressions in LHS will evaluate false
      (depending on a difference of 1 or a difference of >1), resulting in a true implication.





    ** Prove variant bounded below by zero

      I ==> D >= 0

      I: 2 <= i <= n + 1 && res == fact(i - 1)

      Relevant part: 2 <= i <= n + 1

      i <= (n + 1) ==> (n - i) >= 0
      i - 1 <= n ==> n >= i

    * Proof

      Case 1 that would evaluate the expression false: n = 0, i = 1
      However, the invariant protects against i < 2, so this cannot occur.

      Case 2 that would evaluate the expression false: n = 1, i = 2
      However, the invariant ensures that the n parameter becomes n + 1 when evaluated, resulting in n = 2, i = 2, which evaluates to true.

      This proves that the variant is bounded below zero.





    ** Prove decrease expression

      B && I ==> wp(tmp := D ; S, tmp > D)

    * Apply Sequential Rule twice

      wp(tmp := D ; SS1 ; SS2, tmp > D) --> wp(tmp := D, wp(SS1, wp(SS2, tmp > D)))

    * Substitute with actual values

      wp(tmp := D, wp(SS1, wp(SS2, tmp > D))) -->  wp(tmp := n - i, wp(res := res * i, wp(i := i + 1, tmp > n - i)))

    * Apply Assignment Rule once

      wp(tmp := n - i, wp(res := res * i, wp(i := i + 1, tmp > n - i))) --> wp(tmp := n - i, wp(res := res * i, tmp > n - (i + 1)))

                                                                        --> wp(tmp := n - i, wp(res := res * i, tmp > n - i - 1))

                                                                        --> wp(tmp := n - i, tmp > n - i - 1)

                                                                        --> n - i > n - i - 1

    * Recap

      B && I ==> wp(tmp := D ; S, tmp > D)

      B && I ==> n - i > n - i - 1

    * Substitute with actual values

      B && I ==> n - i > n - i - 1 -->

      i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> n - i > n - i - 1

    * Proof

      i <= n && 2 <= i <= n + 1 && res == fact(i - 1) ==> n - i > n - i - 1

      true   && true            && res == fact(2 - 1) ==> n > n - 1

      true   && true            && true/false         ==> true

      true/false                                      ==> true

      true

      This proves the decrementation D.




    ** Prove invariant holds before loop

      Q ==> wp(S1; S2, I)

    * Apply Sequential Rule once

      wp(S1; S2, I) --> wp(S1, wp(S2, I))

    * Substitute with actual values

      wp(S1, wp(S2, I)) --> wp(res := 1, wp(i := 2, 2 <= i <= n + 1 && res == fact(i - 1)))

    * Apply Assignment Rule twice

      wp(res := 1, wp(i := 2, 2 <= i   <= n + 1 && res == fact(i   - 1))) -->

      wp(res := 1,            2 <= (2) <= n + 1 && res == fact((2) - 1))  -->

      wp(res := 1,            2 <= 2   <= n + 1 && res == fact(2   - 1))  -->

                              2 <= 2   <= n + 1 && (1) == fact(2   - 1)   -->

                              2 <= 2   <= n + 1 && 1   == fact(2   - 1)   -->

    * Simplify

      2 <= 2 <= n + 1 && 1 == fact(2 - 1) -->

           2 <= n + 1 && 1 == fact(2 - 1) -->

           2 <= n + 1 && true             -->

           2 <= n + 1                     -->

           2 - 1 <= n                     -->

           1 <= n                         -->

           n >= 1                         -->

    * Recap

      Q ==> n >= 1 --> n > 0 ==> n >= 1

      Trivially true, proving that the invariant holds before loop.





    ** Conclusion

    Since all 5 loop conditions for correct loop are proven true, there's no need
    to change any preconditions since the loop is in itself proven to be true. QED.

    */


*/