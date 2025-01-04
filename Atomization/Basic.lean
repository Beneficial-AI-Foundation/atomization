-- import Lean.Meta

def g := 1

-- inductive TestType
-- | A
-- | B : TestType
-- | C (x : TestType)
-- | D (n : Nat)
-- deriving Repr


def f := 2
def fg := g + g
def f' : 2 = 2 := rfl

theorem f'' : 2 = 2 := by rfl
theorem f''' : 2 = 2 := by omega

def fib : Nat → Nat := fun n =>
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def fibImperative (n: Nat) : Nat := Id.run do
  let mut a : Nat := 0
  let mut b : Nat := 1
  for i in [0:n] do
    let c := a + b
    a := b
    b := c
  return b
-- max's idea of spec: there's 2 functions, one is the recursive one, the other is the imperative one. the recursive one is the 'spec' of the imperative one.

@[csimp]
theorem fib_spec : @fib = @fibImperative := by
  sorry

class inductive InductiveTest
| A
| B : InductiveTest
| C (x : InductiveTest)
| D (n : Nat)
deriving Repr

def trivial' : Nat := 1
def trivial'' : Nat := 1 + 1 - 1
theorem trivial_eq : trivial' = trivial'' := by rfl

mutual

  def even : Nat → Bool
  | 0 => true
  | n + 1 => odd n

  def odd : Nat → Bool
  | 0 => false
  | n + 1 => even n

end
