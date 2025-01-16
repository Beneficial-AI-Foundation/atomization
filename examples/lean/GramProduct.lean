-- set_option autoImplicit false

/--0 is the additive identity-/
class Atom_Zero (α : Type) where
  zero : α

/-- If a type has a zero, then it can use the `0` notation-/
instance {α : Type} [Atom_Zero α] : OfNat α 0 where
  ofNat := Atom_Zero.zero

/--The natural numbers have a zero (of course).-/
instance : Atom_Zero Nat where
  zero := 0

/--A vector is a finite sequence of elements with a fixed length-/
structure Atom_Vector (α : Type) (n : Nat) where
  data : Array α
  _pf : data.size = n
deriving Repr, DecidableEq

/--Indexing a vector in bounds-/
def Atom_Vector.get {α : Type} {n : Nat} (v : Atom_Vector α n) (i : Fin n) : α :=
  --ugh
  have h : i < n := by exact i.isLt
  have h' : n = v.data.size := v._pf.symm
  have h'' : i < v.data.size := Nat.lt_of_lt_of_eq h h'
  v.data[i]'h''

/--Constructing a vector from a function on indices-/
def Atom_Vector.ofFn {α : Type} {n : Nat} (f : Fin n → α) : Atom_Vector α n :=
  { data := Array.ofFn f, _pf := by exact Array.size_ofFn f }

/--Fold a vector-/
def Atom_Vector.foldl {α : Type} {n : Nat} {β : Type}  (v : Atom_Vector α n) (f : β → α → β) (init : β) : β :=
  v.data.foldl f init

/--Zip two vectors with a function-/
def Atom_Vector.zipWith {α : Type} {n : Nat} {β : Type} {γ : Type} (v₁ : Atom_Vector α n) (v₂ : Atom_Vector β n) (f : α → β → γ) : Atom_Vector γ n :=
  Atom_Vector.ofFn (fun i => f (v₁.get i) (v₂.get i))


/--A range of numbers as `Fin`-/
def Array.allFin (n : Nat) : Array (Fin n) :=
  Array.ofFn (fun i => i)

/--A matrix is a vector of vectors-/
abbrev Atom_Matrix (R C : Nat) (α : Type) := Atom_Vector (Atom_Vector α C) R

/--Display a matrix-/
instance {R C : Nat} {α : Type} [ToString α] : Repr (Atom_Matrix R C α) where
  reprPrec m _ := Id.run do
    let mut s := ""
    for r in Array.allFin R do
      for c in Array.allFin C do
        s := s ++ s!"{m.get r |>.get c} "
      s := s ++ "\n"
    return s

def Atom_Matrix.toString [ToString α] (m : Atom_Matrix R C α) : String :=
  s!"{repr m}"

-- /--Display a matrix-/
-- instance [ToString α] : ToString (Matrix R C α) where
--   toString := fun m => s!"{repr m}"

-- def a : Atom_Vector Nat 3 := Atom_Vector.ofFn (fun i => i)
-- #eval a

def Atom_Vector.sum {α : Type} {C : Nat} [Add α] [Atom_Zero α] (v : Atom_Vector α C) : α :=
  v.foldl (· + ·) 0

def Atom_Vector.dot {α : Type} {R : Nat} {β : Type} {γ : Type} [HMul α β γ] [Add γ][Atom_Zero γ] (v₁:Atom_Vector α R) (v₂ : Atom_Vector β R) : γ :=
  v₁.zipWith v₂ (· * ·) |>.sum

def Atom_Vector.scalar_multiplication {α β γ : Type} {n : Nat} [HMul α β γ]  (a : α)  (v : Atom_Vector β n) : Atom_Vector γ n :=
  Atom_Vector.ofFn (fun i => a * v.get i)

-- /-- Scalar multiplication of a vector on the left-/
-- instance [HMul α β γ] : HMul α (Vector β n) (Vector γ n) where
--   hMul a v := Vector.ofFn (fun i => a * v.get i)

def Atom_Matrix.matvec_mul {α β γ : Type} {R C : Nat} [HMul α β γ] [Add γ] [Atom_Zero γ] (m : Atom_Matrix R C α) (v : Atom_Vector β C) : Atom_Vector γ R :=
  Atom_Vector.ofFn (fun r => (m.get r).dot v)

-- instance [HMul α β γ] [Add γ] [Zero γ] : HMul (Matrix R C α) (Vector β C) (Vector γ R) where
--   hMul m v := matvec_mul m v

/--Constructing a matrix from a function on indices-/
def Atom_Matrix.ofFn {α : Type} {R C : Nat} (f : Fin R → Fin C → α) : Atom_Matrix R C α :=
  Atom_Vector.ofFn (fun r => Atom_Vector.ofFn (fun c => f r c))

def Atom_A : Atom_Matrix 3 2 Nat := Atom_Vector.ofFn (fun r => Atom_Vector.ofFn (fun c => r * c))
def Atom_B : Atom_Matrix 2 3 Nat := Atom_Vector.ofFn (fun c => Atom_Vector.ofFn (fun r => c * r))

def Atom_Vector.toMatrix {α : Type} {R : Nat} (vec : Atom_Vector α R) : Atom_Matrix R 1 α :=
  Atom_Vector.ofFn (fun i => Atom_Vector.ofFn (fun _ => vec.get i))

def Atom_Matrix.transpose {α : Type} {R C : Nat} (A : Atom_Matrix R C α) : Atom_Matrix C R α :=
  Atom_Vector.ofFn (fun c => Atom_Vector.ofFn (fun r => (A.get r).get c))

def Atom_Matrix.mul {α β γ: Type} {R J C : Nat} [HMul α β γ] [Add γ] [Atom_Zero γ] (A : Atom_Matrix R J α) (B : Atom_Matrix J C β) : Atom_Matrix R C γ :=
  let B' := B.transpose
  Atom_Vector.ofFn (fun r => Atom_Vector.ofFn (fun j => (A.get r).dot (B'.get j)))


def Atom_Matrix.test_mul : Atom_Matrix 3 3 Nat := Atom_A.mul Atom_B

#eval Atom_Matrix.test_mul
