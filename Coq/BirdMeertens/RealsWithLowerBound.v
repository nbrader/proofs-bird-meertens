Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope R_scope.

Module RealsWithLowerBound.
Definition RLB := option R.


Section RLBmax.
Definition RLBmax (x y : RLB) : RLB :=
  match x, y with
  | None, _ => y
  | _, None => x
  | Some a, Some b => Some (Rmax a b)
  end.

Lemma RLBmax_comm : forall x y : RLB, RLBmax x y = RLBmax y x.
Proof.
  intros x y; destruct x, y; simpl; try reflexivity.
  - f_equal.
    apply Rmax_comm.
Qed.

Lemma RLBmax_assoc : forall x y z : RLB, RLBmax x (RLBmax y z) = RLBmax (RLBmax x y) z.
Proof.
  intros x y z; destruct x, y, z; simpl; try reflexivity.
  - rewrite Rmax_assoc; reflexivity.
Qed.

Lemma Rmax_idempotent : forall x : R, Rmax x x = x.
Proof.
  intros.
  unfold Rmax.
  case (Rle_dec x x); intros; reflexivity.
Qed.

Lemma RLBmax_idempotent : forall x : RLB, RLBmax x x = x.
Proof.
  intros x; destruct x; simpl; try reflexivity.
  - f_equal.
    apply Rmax_idempotent.
Qed.

Lemma RLBmax_left_id : forall x : RLB, RLBmax None x = x.
Proof.
  intro x.
  unfold RLBmax.
  reflexivity.
Qed.

Lemma RLBmax_right_id : forall x : RLB, RLBmax x None = x.
Proof.
  intro x.
  unfold RLBmax.
  induction x; reflexivity.
Qed.
End RLBmax.


Section RLBplus.
Definition RLBplus (x y : RLB) : RLB :=
  match x, y with
  | None, _ | _, None => None  (* Treat None as 'undefined' for sum *)
  | Some a, Some b => Some (a + b)
  end.

Lemma RLBplus_comm : forall x y : RLB, RLBplus x y = RLBplus y x.
Proof.
  intros x y; destruct x, y; simpl; try reflexivity.
  - f_equal; apply Rplus_comm.
Qed.

Lemma RLBplus_assoc : forall x y z : RLB, RLBplus x (RLBplus y z) = RLBplus (RLBplus x y) z.
Proof.
  intros x y z; destruct x, y, z; simpl; try reflexivity.
  - f_equal; rewrite Rplus_assoc; reflexivity.
Qed.
End RLBplus.


Section RLBsum.
Definition RLBsum : list RLB -> RLB := fun xs => fold_right RLBplus None xs.
End RLBsum.


End RealsWithLowerBound.

Export RealsWithLowerBound.