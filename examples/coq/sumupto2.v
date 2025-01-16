From Coq Require Import List Arith Lia.

Definition sum_upto (n : nat) : nat :=
  fold_left plus (seq 0 (S n)) 0.

Fixpoint sum_upto_rec (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => S n' + sum_upto_rec n'
  end.

Definition spec (n : nat) : nat := Nat.div (n * (n + 1)) 2.

Lemma x : forall n m (f : nat -> nat -> nat), fold_left f (seq n m) = fold_left f (rev (seq n m)).
Proof.
  intros n m f.
  induction m; auto.
  simpl.
  Admitted.

Lemma fold_left_seq_0 : forall n, fold_left plus (seq 0 n) 0 = fold_left plus (seq 0 (S n)) 0 - n.
Proof.
  intros n.
  induction n; auto.
  simpl seq; simpl fold_left.
  simpl seq in IHn; simpl fold_left in IHn.
  Admitted.

Lemma y n : S (n + 1) = n + 2.
Proof. lia. Qed.
Lemma z n : S n + 1 = n + 2.
Proof. lia. Qed.

Lemma g : forall n, Nat.Even n \/ Nat.Even (S n).
Proof.
  intros n; unfold Nat.Even.
  induction n.
  * left.
    exists 0.
    reflexivity.
  * destruct IHn; destruct H; subst.
    right.
    exists (x0 + 1).
    lia.
    left.
    rewrite H.
    exists x0.
    reflexivity.
Qed.

Lemma b : forall n, S n * (S n + 1) / 2 = n + 1 + n * (n + 1) / 2.
Proof.
  intros n.
  induction n; auto.
  destruct g with (n := n); unfold Nat.Even in H; destruct H.
  * subst.

  rewrite <- Nat.mul_cancel_l with (p := 2); auto.
  rewrite Nat.mul_add_distr_l.
  rewrite Nat.add_1_r.
  rewrite Nat.mul_add_distr_l.

  inversion g.
  destruct (Nat.Even n \/ Nat.Even (S n)).
Admitted.

Lemma c : forall n, fold_left Init.Nat.add (seq 2 n) 1 = n + 1 + fold_left Init.Nat.add (seq 1 n) 0.
Proof.
  intros n.
  Admitted.

Theorem correctness : forall n, sum_upto n = spec n.
Proof.
  intros n.
  unfold sum_upto, spec.
  simpl seq; simpl fold_left.
  induction n; auto.
  rewrite <- Nat.add_cancel_l with (p := (n + 1)) in IHn.
  rewrite b.
  rewrite <- IHn.
  simpl.
  simpl seq in IHn; simpl fold_left in IHn.
  rewrite c.
  reflexivity.
Qed.
