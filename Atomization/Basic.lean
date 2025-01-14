/-!
# Atomization

All the identifiers start with `Atom_` to make them easy to filter so I can test the atomization fast.
-/

def Atom_g := 1
-- import Mathlib.Tactic.Ring
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Tactic.FieldSimp
-- import Lean.Meta


-- inductive Atom_TestType
-- | A
-- | B : Atom_TestType
-- | C (x : Atom_TestType)
-- | D (n : Nat)
-- deriving Repr


def Atom_f := 2
def Atom_fg := Atom_g + Atom_g
def Atom_f' : 2 = 2 := rfl

theorem Atom_f'' : 2 = 2 := by rfl
theorem Atom_f''' : 2 = 2 := by omega

def Atom_fib : Nat → Nat := fun n =>
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => Atom_fib (n + 1) + Atom_fib n

def Atom_fibImperative (n: Nat) : Nat := Id.run do
  let mut a : Nat := 0
  let mut b : Nat := 1
  for i in [0:n] do
    let c := a + b
    a := b
    b := c
  return b
-- max's idea of spec: there's 2 functions, one is the recursive one, the other is the imperative one. the recursive one is the 'spec' of the imperative one.

@[csimp]
theorem Atom_fib_spec : @Atom_fib = @Atom_fibImperative := by
  sorry



def Atom_trivial : Nat := 1
def Atom_trivial_ : Nat := 1 + 1 - 1
theorem Atom_trivial_eq : Atom_trivial = Atom_trivial_ := by rfl

mutual

  def Atom_even : Nat → Bool
  | 0 => true
  | n + 1 => Atom_odd n

  def Atom_odd : Nat → Bool
  | 0 => false
  | n + 1 => Atom_even n
end



def Atom_sumUpTo (n : Nat) : Nat := match n with
  | 0 => 0
  | n+1 => n + 1 + Atom_sumUpTo n

def Atom_fastSumUpTo (n : Nat) : Nat := n * (n + 1) / 2

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



theorem Atom_split_sum (n : Nat) : Atom_sumUpTo (n + 1) = n + 1 + Atom_sumUpTo n := by simp [Atom_sumUpTo]


-- theorem sumUpTo_eq_fastSumUpTo (n : Nat) : sumUpTo n = fastSumUpTo n := by
--   induction n with
--   | zero => rfl
--   | succ n ih => calc
--     sumUpTo (n + 1) = n + 1 + sumUpTo n := splitSum n
--     _ = n + 1 + fastSumUpTo n := by rw [ih]
--     _ = fastSumUpTo (n + 1) := by splitFastSum (n+1)
namespace Atom_Test
  def f := 1
  def g := 2
  def h := f + g
end Atom_Test
