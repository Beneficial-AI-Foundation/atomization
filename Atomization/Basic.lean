def g := 1
-- import Mathlib.Tactic.Ring
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Tactic.FieldSimp
-- import Lean.Meta


inductive TestType
| A
| B : TestType
| C (x : TestType)
| D (n : Nat)
deriving Repr


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



def sumUpTo (n : Nat) : Nat := match n with
  | 0 => 0
  | n+1 => n + 1 + sumUpTo n

def fastSumUpTo (n : Nat) : Nat := n * (n + 1) / 2

-- theorem splitFastSum (n : Nat) : fastSumUpTo (n+1) = n + 1 + fastSumUpTo n := by simp [fastSumUpTo]
--   induction n with
--   | zero => rfl
--   | succ n ih =>
--     unfold fastSumUpTo
--     ring_nf
--     sorry

    -- calc
    --   (n + 1) * (n + 2) / 2
    --     = (n + 1) + n * (n + 1) / 2 := by ring_nf
    --   _ = (n + 1) + fastSumUpTo n := by rw [ih]



theorem split_sum (n : Nat) : sumUpTo (n + 1) = n + 1 + sumUpTo n := by simp [sumUpTo]


-- theorem sumUpTo_eq_fastSumUpTo (n : Nat) : sumUpTo n = fastSumUpTo n := by
--   induction n with
--   | zero => rfl
--   | succ n ih => calc
--     sumUpTo (n + 1) = n + 1 + sumUpTo n := splitSum n
--     _ = n + 1 + fastSumUpTo n := by rw [ih]
--     _ = fastSumUpTo (n + 1) := by splitFastSum (n+1)
namespace Test
  def f := 1
  def g := 2
  def h := f + g
end Test
