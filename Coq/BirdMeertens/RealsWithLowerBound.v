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


Section RLBmax.
Definition RLBmax (x y : RLB) : RLB :=
  match x, y with
  | neg_inf, _ => y
  | _, neg_inf => x
  | finite a, finite b => finite (Rmax a b)
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

Lemma RLBmax_left_id : forall x : RLB, RLBmax neg_inf x = x.
Proof.
  (* exact (fun x => eq_refl). *)
  intro x; reflexivity.
Qed.

Lemma RLBmax_right_id : forall x : RLB, RLBmax x neg_inf = x.
Proof.
  (* exact (fun x : RLB => option_ind (fun x0 : option R => RLBmax x0 None = x0) (fun a : R => eq_refl) eq_refl x). *)
  intro x; induction x; reflexivity.
Qed.
End RLBmax.


Section RLBplus.
Definition RLBplus (x y : RLB) : RLB :=
  match x, y with
  | neg_inf, _ | _, neg_inf => neg_inf  (* Add anything to negative infinity and you get negative infinity. *)
  | finite a, finite b => finite (a + b)
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

Lemma RLBplus_left_id : forall x : RLB, RLBplus (finite 0) x = x.
Proof.
  intro x.
  unfold RLBplus.
  induction x.
    - f_equal.
      ring.
    - reflexivity.
Qed.

Lemma RLBplus_right_id : forall x : RLB, RLBplus x (finite 0) = x.
Proof.
  intro x.
  unfold RLBplus.
  induction x.
    - f_equal.
      ring.
    - reflexivity.
Qed.
End RLBplus.


Section RLBlte.
Definition RLBlte (x y : RLB) : Prop :=
  match x, y with
  | neg_inf, _ => True   (* Negative infinity is less or equal to everything. *)
  | _, neg_inf => False  (* Anything (other than negative infinity) is greater than negative infinity. *)
  | finite a, finite b => a <= b
  end.
End RLBlte.

End RealsWithLowerBound.

Export RealsWithLowerBound.