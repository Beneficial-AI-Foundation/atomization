// fibonnaci function
function fibonacci(n: int): int
    requires n >= 0
    decreases n
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
        decreases n - i
    {
        var c := a + b;
        a := b;
        b := c;
        i := i + 1;
    }
}