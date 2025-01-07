set_option autoImplicit true

variable {R C J : Nat} {α : Type} [Add α] [Mul α] [Zero α]

abbrev Matrix (R C : Nat) (α : Type) := Vector (Vector α C) R

instance [ToString α] : Repr (Matrix R C α) where
  reprPrec m _ := Id.run do
    let mut s := ""
    for r in Array.finRange R do
      for c in Array.finRange C do
        s := s ++ s!"{m.get r |>.get c} "
      s := s ++ "\n"
    return s

instance [ToString α] : ToString (Matrix R C α) where
  toString := fun m => s!"{repr m}"

def A : Matrix 3 2 Nat := Vector.ofFn (fun r => Vector.ofFn (fun c => r * c))
def B : Matrix 2 3 Nat := Vector.ofFn (fun c => Vector.ofFn (fun r => c * r))

#eval A
#eval B



def Vector.sum (v : Vector α C) : α :=
  v.foldl (· + ·) 0

def Vector.dot (v₁ v₂ : Vector α R) : α :=
  v₁.zipWith v₂ (· * ·) |>.sum

def Vector.toMatrix (vec : Vector α R) : Matrix R 1 α :=
  Vector.ofFn (fun i => #v[vec.get i])

def Matrix.transpose (A : Matrix R C α) : Matrix C R α :=
  Vector.ofFn (fun c => Vector.ofFn (fun r => (A.get r).get c))

def Matrix.mul (A : Matrix R J α) (B : Matrix J C α) : Matrix R C α :=
  let B' := B.transpose
  Vector.ofFn (fun r => Vector.ofFn (fun j => Vector.dot (A.get r) (B'.get j)))


def test_mul : Matrix 3 3 Nat := A.mul B

#eval test_mul
