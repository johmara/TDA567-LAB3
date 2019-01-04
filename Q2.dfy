// Question 2

method Q2(x : int, y : int) returns (big : int, small : int)
  ensures big > small;
{
  if (x > y)
   {big, small := x, y;}
  else
   {big, small := y, x;}
}

/*
The postcondition wont hold because you can't ensure that big is greater than small, EX: if x = y big wont be greater.

    Q: None
    R: big > small
    S: if (x > y) then {big, small := x, y;} else {big, small := y, x;}

	Apply Seq-rule:
	
	wp(if (x > y) then {big, small := x, y;} else {big, small := y, x;},R)
	
		 
	Apply Conditional-rule:
	
	x > y  ==> wp(big, small := x, y, R) && 
	x <= y ==> wp(big, small := y, x, R) 
	
	
	Apply Assignment to the if-branch:

	x > y ==> wp(big := x , wp(small := y, R))
	x > y ==> big > small
	
	Apply Assignment to the else-branch:
	
	x <= y ==> wp(big := y , wp(small := x, R))
	x <= y ==> big <= small

	This shows that if the inputs are equal the program will fail.
	
----------------------------------------------------------------------------------------------------------------------
Q ==> wp(S,R) ->
    Q ==> wp (S,R) ->
    None ==> wp( if (x > y) then {big, small := x, y;} else {big, small := y, x;} , big > small)
            conditional rule and assignment rule.

    conditional rule:
    ((x > y) -> wp({big, small := x, y;},(big > small))) &&
    ((x <= y) -> wp({big, small := y, x;},(big > small)))

    Assignment rule:
    (x > y ==> big, small := x, y) && (x <= y ==> big, small := y, x) = true && false = false

    This shows that if the inputs are equal the program will fail.

1:
    Add a requires as seen below.

    method Q2(x : int, y : int) returns (big : int, small : int)
      requires x != y;
      ensures big > small;
    {
      if (x > y)
       {big, small := x, y;}
      else
       {big, small := y, x;}
    }

2:
    Change ensure to be as below.

    method Q2(x : int, y : int) returns (big : int, small : int)
      ensures big >= small;
    {
      if (x > y)
       {big, small := x, y;}
      else
       {big, small := y, x;}
    }

3:
    It is possible by adding an else wich assigns dummy values if x and y are equal however that would defeat the
    purpose of the program.

    Example:
    method Q2(x : int, y : int) returns (big : int, small : int)
          ensures big >= small;
        {
          if (x > y)
           {big, small := x, y;}
          else if (x < y)
           {big, small := y, x;}
          else
           {big, small := 1, 0}
        }

*/
