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
  (* exact (fun x => eq_refl). *)
  intro x; reflexivity.
Qed.

Lemma RLB_max_right_id : forall x : RLB, RLB_max x neg_inf = x.
Proof.
  (* exact (fun x : RLB => option_ind (fun x0 : option R => RLB_max x0 None = x0) (fun a : R => eq_refl) eq_refl x). *)
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


Section RLB_lte.
Definition RLB_lte (x y : RLB) : Prop :=
  match x, y with
  | neg_inf, _ => True   (* Negative infinity is less or equal to everything. *)
  | _, neg_inf => False  (* Anything (other than negative infinity) is greater than negative infinity. *)
  | finite a, finite b => a <= b
  end.
End RLB_lte.

End RealsWithLowerBound.

Export RealsWithLowerBound.