set_option autoImplicit true

/--0 is the additive identity-/
class Zero (α : Type) where
  zero : α

/-- If a type has a zero, then it can use the `0` notation-/
instance [Zero α] : OfNat α 0 where
  ofNat := Zero.zero

/--The natural numbers have a zero (of course).-/
instance : Zero Nat where
  zero := 0

/--A vector is a finite sequence of elements with a fixed length-/
structure Vector (α : Type) (n : Nat) where
  data : Array α
  _pf : data.size = n
deriving Repr,DecidableEq

/--Indexing a vector in bounds-/
def Vector.get (v : Vector α n) (i : Fin n) : α :=
  --ugh
  have h : i < n := by exact i.isLt
  have h' : n = v.data.size := v._pf.symm
  have h'' : i < v.data.size := Nat.lt_of_lt_of_eq h h'
  v.data[i]'h''

/--Constructing a vector from a function on indices-/
def Vector.ofFn (f : Fin n → α) : Vector α n :=
  { data := Array.ofFn f, _pf := by exact Array.size_ofFn f }


/--Fold a vector-/
def Vector.foldl (v : Vector α n) (f : β → α → β) (init : β) : β :=
  v.data.foldl f init

/--Zip two vectors with a function-/
def Vector.zipWith (v₁ : Vector α n) (v₂ : Vector β n) (f : α → β → γ) : Vector γ n :=
  Vector.ofFn (fun i => f (v₁.get i) (v₂.get i))

/--Map a vector-/
def Vector.map (v : Vector α n) (f : α → β) : Vector β n :=
  Vector.ofFn (fun i => f (v.get i))

/--A range of numbers as `Fin`-/
def Array.allFin (n : Nat) : Array (Fin n) :=
  Array.ofFn (fun i => i)

variable {R C J : Nat} {α : Type} [Add α] [Mul α] [Zero α]

/--A matrix is a vector of vectors-/
abbrev Matrix (R C : Nat) (α : Type) := Vector (Vector α C) R

/--Display a matrix-/
instance [ToString α] : Repr (Matrix R C α) where
  reprPrec m _ := Id.run do
    let mut s := ""
    for r in Array.allFin R do
      for c in Array.allFin C do
        s := s ++ s!"{m.get r |>.get c} "
      s := s ++ "\n"
    return s

/--Display a matrix-/
instance [ToString α] : ToString (Matrix R C α) where
  toString := fun m => s!"{repr m}"

def a : Vector  Nat 3 := Vector.ofFn (fun i => i)
#eval a

def Vector.sum (v : Vector α C) : α :=
  v.foldl (· + ·) 0

def Vector.dot [HMul α β γ] [Add γ][Zero γ] (v₁:Vector α R) (v₂ : Vector β R) : γ :=
  v₁.zipWith v₂ (· * ·) |>.sum

/-- Scalar multiplication of a vector on the left-/
instance [HMul α β γ] : HMul α (Vector β n) (Vector γ n) where
  hMul a v := Vector.ofFn (fun i => a * v.get i)



instance [HMul α β γ] [Add γ] [Zero γ] : HMul (Matrix R C α) (Vector β C) (Vector γ R) where
  hMul m v := Vector.ofFn (fun r => (m.get r).dot v)

/--Constructing a matrix from a function on indices-/
def Matrix.ofFn (f : Fin R → Fin C → α) : Matrix R C α :=
  Vector.ofFn (fun r => Vector.ofFn (fun c => f r c))


def A : Matrix 3 2 Nat := Vector.ofFn (fun r => Vector.ofFn (fun c => r * c))
def B : Matrix 2 3 Nat := Vector.ofFn (fun c => Vector.ofFn (fun r => c * r))

#eval (2 * A, A)
#eval B

def Vector.toMatrix (vec : Vector α R) : Matrix R 1 α :=
  Vector.ofFn (fun i => Vector.ofFn (fun _ => vec.get i))

#eval a.toMatrix

def Matrix.transpose (A : Matrix R C α) : Matrix C R α :=
  Vector.ofFn (fun c => Vector.ofFn (fun r => (A.get r).get c))

def Matrix.mul (A : Matrix R J α) (B : Matrix J C α) : Matrix R C α :=
  let B' := B.transpose
  Vector.ofFn (fun r => .ofFn (fun j => (A.get r).dot (B'.get j)))


def test_mul : Matrix 3 3 Nat := A.mul B

#eval test_mul
