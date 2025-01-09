(* from Temo *)
From Coq Require Import Ring.
From Coq Require Import Arith.

Fixpoint sum_recursive (n : nat) : nat :=
  match n with
  | 0 => 0
  | (S n') => n + (sum_recursive n')
  end.

Theorem sum_formula : forall n, 2 * (sum_recursive n) = (n + 1) * n.
Proof. intros n. induction n.
       - reflexivity. (* 0 = 0 base case *)
       - simpl. ring [IHn]. (* induction step *)
Qed.
