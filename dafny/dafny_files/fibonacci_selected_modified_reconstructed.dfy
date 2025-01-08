ghost function fibonacci(n: int): int
   requires n >= 0
   decreases n
   ensures fibonacci(n) >= 0
{
  if n == 0 then 0
  else if n == 1 then 1
  else fibonacci(n-1) + fibonacci(n-2)
}



method fib_method(n: int) returns (result: int)
   requires n >= 0
   ensures result == fibonacci(n)
{
  var i: int := 0;
  var a: int := 0;
  var b: int := 1;
  while i < n
   invariant 0 <= a
   invariant 0 <= i <= n
   invariant a == fibonacci(i)
   invariant b == fibonacci(i + 1)
   invariant 0 <= b
   decreases n - i
  {
    var c := a + b;
    a := b;
    b := c;
    i := i + 1;
  }
  result := a;
}

function fibonacci2(n: int): int
   requires n >= 0
   decreases n
   ensures fibonacci2(n) == fibonacci(n)
{
  if n == 0 then 0
  else if n == 1 then 1
  else fibonacci2(n-1) + fibonacci2(n-2)
}


ghost function FibNonNegative(n: int): bool
{
  forall k :: k >= 0 ==> fibonacci(k) >= 0
}



ghost predicate IsFibonacci(x: int)
{
  exists n :: n >= 0 && fibonacci(n) == x
}

lemma FibIsNonNegative(n: int)
   requires n >= 0
   ensures fibonacci(n) >= 0
{
  if n <= 1 {

  } else {

    FibIsNonNegative(n-1);
    FibIsNonNegative(n-2);

  }
}
