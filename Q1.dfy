//Question 1:

method Abs(x : int) returns (y : int)
  // return value doesn't deviate from intended value
  ensures 0 <= x ==> y == x;
  ensures x < 0 ==> y == -x;
   // return value is greater or equal to zero
  ensures 0 <= y;
{
  if (x < 0)
   { y := -x; }
  else
   { y := x; }
}

/*
1: We don't have any preconditions and we don't need any since the postconditions covers every possible value of x.

2:
    Q: None
    R1: 0 <= x ==> y == x
    R2: x < 0 ==> y == -x
    R3: 0 <= y
    S: if(x < 0) then {y := -x} else {y := x }

    Q ==> wp(S,R) ->
    None ==> wp( if(x < 0) then {y := -x} else {y := x }, (0 <= x ==> y == x) && (x < 0 ==> y == -x) && (0 <= y)) ->
                Conditional rule and assignment rule

    Conditional rule:
    ((x < 0) -> wp({y := -x}, (0 <= x ==> y == x) && (x < 0 ==> y == -x) && (0 <= y))) &&
    ((0 <= x) -> wp({y := x}, (0 <= x ==> y == x) && (x < 0 ==> y == -x) && (0 <= y)))

    Assignment rule:
    (x < 0 ==> y := -x) && (0 <= x ==> y := x) = true && true = true

3:
    Since the purpose of the abs method is that it should calculate and return an absolute of the number inserted we do
    not need to mutate the in-parameter, we just assign what should be returned to a local variable instead. This means
    that a function could have been used instead of a method, therefore it's a design mistake.

*/