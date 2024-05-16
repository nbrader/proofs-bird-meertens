Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope R_scope.

Module RealsWithLowerBound.
Inductive RLB :=
  | finite (r : R)
  | neg_inf.

Definition RLB_to_option (x : RLB) : option R := match x with
  | finite r => Some r
  | neg_inf => None
end.

Definition option_to_RLB (x : option R) : RLB := match x with
  | Some r => finite r
  | None => neg_inf
end.

Section RLB_max.
Definition RLB_max (x y : RLB) : RLB :=
  match x, y with
  | neg_inf, _ => y
  | _, neg_inf => x
  | finite a, finite b => finite (Rmax a b)
  end.

Lemma RLB_max_comm : forall x y : RLB, RLB_max x y = RLB_max y x.
Proof.
  intros x y; destruct x, y; simpl; try reflexivity.
  - f_equal.
    apply Rmax_comm.
Qed.

Lemma RLB_max_assoc : forall x y z : RLB, RLB_max x (RLB_max y z) = RLB_max (RLB_max x y) z.
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

Lemma RLB_max_idempotent : forall x : RLB, RLB_max x x = x.
Proof.
  intros x; destruct x; simpl; try reflexivity.
  - f_equal.
    apply Rmax_idempotent.
Qed.

Lemma RLB_max_left_id : forall x : RLB, RLB_max neg_inf x = x.
Proof.
  intro x; reflexivity.
Qed.

Lemma RLB_max_right_id : forall x : RLB, RLB_max x neg_inf = x.
Proof.
  intro x; induction x; reflexivity.
Qed.
End RLB_max.

Section RLB_plus.
Definition RLB_plus (x y : RLB) : RLB :=
  match x, y with
  | neg_inf, _ | _, neg_inf => neg_inf  (* Add anything to negative infinity and you get negative infinity. *)
  | finite a, finite b => finite (a + b)
  end.

Lemma RLB_plus_comm : forall x y : RLB, RLB_plus x y = RLB_plus y x.
Proof.
  intros x y; destruct x, y; simpl; try reflexivity.
  - f_equal; apply Rplus_comm.
Qed.

Lemma RLB_plus_assoc : forall x y z : RLB, RLB_plus x (RLB_plus y z) = RLB_plus (RLB_plus x y) z.
Proof.
  intros x y z; destruct x, y, z; simpl; try reflexivity.
  - f_equal; rewrite Rplus_assoc; reflexivity.
Qed.

Lemma RLB_plus_left_id : forall x : RLB, RLB_plus (finite 0) x = x.
Proof.
  intro x.
  unfold RLB_plus.
  induction x.
    - f_equal.
      ring.
    - reflexivity.
Qed.

Lemma RLB_plus_right_id : forall x : RLB, RLB_plus x (finite 0) = x.
Proof.
  intro x.
  unfold RLB_plus.
  induction x.
    - f_equal.
      ring.
    - reflexivity.
Qed.
End RLB_plus.

Section RLB_le.
Definition RLB_le (x y : RLB) : Prop :=
  match x, y with
  | neg_inf, _ => True   (* Negative infinity is less or equal to everything. *)
  | _, neg_inf => False  (* Everything (other than negative infinity) is greater than negative infinity. *)
  | finite a, finite b => a <= b
  end.

Definition RLB_le_dec (x y : RLB) : {RLB_le x y} + {~ RLB_le x y}.
Proof.
  destruct x, y; simpl.
  - destruct (Rle_dec r r0); [left | right]; assumption.
  - right. intro. apply H.
  - left. exact I.
  - left. exact I.
Qed.
End RLB_le.

Section RLB_ge.
Definition RLB_ge (x y : RLB) : Prop :=
  match x, y with
  | _, neg_inf => True   (* Negative infinity is less or equal to everything. *)
  | neg_inf, _ => False  (* Everything (other than negative infinity) is greater than negative infinity. *)
  | finite a, finite b => b <= a
  end.
End RLB_ge.

Definition RLB_nonNegPlus (x y : RLB) : RLB :=
  if RLB_le_dec (finite 0) (RLB_plus x y) then RLB_plus x y else finite 0.
Notation "x <#> y" := (RLB_nonNegPlus x y) (at level 50, left associativity).

Definition RLB_nonNegSum : list RLB -> RLB := fold_right RLB_nonNegPlus (finite 0).

Lemma RLB_nonNegPlusEitherPlusOr0 : forall (x y : RLB),
  x <#> y = if RLB_le_dec (finite 0) (RLB_plus x y) then RLB_plus x y else finite 0.
Proof.
  intros x y.
  unfold RLB_nonNegPlus.
  destruct (RLB_le_dec (finite 0) (RLB_plus x y)); reflexivity.
Qed.

End RealsWithLowerBound.

Export RealsWithLowerBound.
