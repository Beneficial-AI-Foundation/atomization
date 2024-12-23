









method fib_method(n: int) returns (result: int)
{
  var i: int := 0;
  var a: int := 0;
  var b: int := 1;
  while i < n
  {
    var c := a + b;
    a := b;
    b := c;
    i := i + 1;
  }
  result := a;
}

ghost function fibonacci(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else if n == 1 then 1
  else fibonacci(n-1) + fibonacci(n-2)
}


ghost function FibNonNegative(n: int): bool
{
  forall k :: k >= 0 ==> fibonacci(k) >= 0
}



