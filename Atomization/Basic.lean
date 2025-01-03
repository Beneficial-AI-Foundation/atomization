import Lean.Meta

def g := 1

-- #eval Lean.Meta.inferType `f
def f := 2
def fg := g + g
def f' : 2 = 2 := rfl

theorem f'' : 2 = 2 := by rfl

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



def fib': Nat -> Nat := fun n =>
  (let a := 0;
      let b := 1;
      do
        let r ←
          -- let col := [0:n];
          forIn [0:n] ⟨a, b⟩ fun i r =>
            let a := r.fst;
            let b := r.snd;
            let c := a + b;
            let a := b;
            let b := c;
            do
                pure PUnit.unit
                pure (ForInStep.yield ⟨a, b⟩)
        match r with
          | ⟨a, b⟩ => pure b).run
