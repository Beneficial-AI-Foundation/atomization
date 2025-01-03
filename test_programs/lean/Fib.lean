
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def fib' : Nat → Nat :=
  fun n =>
    match n with
    | 0 => 0
    | 1 => 1
    | n + 2 => fib' (n + 1) + fib' n

def fibFast (n: Nat) : Nat := Id.run do
  let mut a := 0
  let mut b := 1
  for i in [0:n] do
    let c := a + b
    a := b
    b := c
  return b



#eval fib 20 -- 55
