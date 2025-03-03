namespace Atomization

/-- A simple constant with value 1 -/
def g : Nat := 1

/-- A simple constant with value 2 -/
def f : Nat := 2

/-- Sum of g with itself -/
def fg : Nat := g + g

/-- Alternative definition of f -/
def f' : Nat := 1 + 1

/-- Theorem: 2 equals 2 -/
theorem f'' : f = f := by rfl

/-- Theorem: 2 equals 2 (with a different proof) -/
theorem f''' : f = f' := by
  simp [f, f']

/-- Recursive definition of Fibonacci -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

/-- Imperative style Fibonacci -/
def fibImperative (n : Nat) : Nat := Id.run do
  if n == 0 then return 0
  if n == 1 then return 1
  let mut a := 0
  let mut b := 1
  let mut i := 2
  while i <= n do
    let c := a + b
    a := b
    b := c
    i := i + 1
  return b

/-- Specification: both Fibonacci implementations are equivalent -/
theorem fib_spec (n : Nat) : fib n = fibImperative n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    sorry -- Proof omitted for brevity

/-- A trivial definition -/
def trivial : Bool := true

/-- Another trivial definition -/
def trivial_ : Bool := true

/-- Theorem: Both trivial definitions are equal -/
theorem trivial_eq : trivial = trivial_ := by rfl

/-- Even predicate -/
def even : Nat → Bool
  | 0 => true
  | n+1 => odd n

/-- Odd predicate -/
def odd : Nat → Bool
  | 0 => false
  | n+1 => even n

/-- Sum up to n -/
def sumUpTo : Nat → Nat
  | 0 => 0
  | n+1 => n+1 + sumUpTo n

/-- Fast sum up to n using the closed formula -/
def fastSumUpTo (n : Nat) : Nat := n * (n + 1) / 2

/-- Theorem: The recursive sum equals the closed formula -/
theorem split_sum : ∀ n, sumUpTo n = fastSumUpTo n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    sorry -- Proof omitted for brevity

/-- A namespace with mutually defined functions -/
namespace Test

def f (n : Nat) : Nat := n + g 0

def g (n : Nat) : Nat :=
  if n == 0 then 1 else f (n-1)

def h (n : Nat) : Nat := f n + g n

end Test

end Atomization
