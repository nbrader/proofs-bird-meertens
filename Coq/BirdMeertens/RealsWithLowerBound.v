Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope R_scope.

Require Import Psatz.

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

(* Section RLB_order. *)
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

Definition RLB_ge (x y : RLB) : Prop :=
  match x, y with
  | _, neg_inf => True   (* Negative infinity is less or equal to everything. *)
  | neg_inf, _ => False  (* Everything (other than negative infinity) is greater than negative infinity. *)
  | finite a, finite b => b <= a
  end.
(* End RLB_order. *)

(* Section RLB_max. *)
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

Lemma RLB_max_implementation (x y : RLB) : RLB_max x y = if RLB_le_dec x y then y else x.
Proof.
  destruct (RLB_le_dec x y).
  - case x, y.
    + unfold RLB_le in r.
      unfold RLB_max.
      f_equal.
      unfold Rmax.
      destruct Rle_dec.
      * reflexivity.
      * contradiction.
    + unfold RLB_le in r.
      contradiction.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - case x, y.
    + unfold RLB_le in n.
      unfold RLB_max.
      f_equal.
      unfold Rmax.
      destruct Rle_dec.
      * contradiction.
      * reflexivity.
    + unfold RLB_le in r.
      reflexivity.
    + exfalso.
      apply n.
      unfold RLB_le.
      exact I.
    + simpl.
      reflexivity.
Qed.
(* End RLB_max. *)


(* Section RLB_plus. *)
Definition RLB_plus (x y : RLB) : RLB :=
  match x, y with
  | neg_inf, _ | _, neg_inf => neg_inf  (* Add anything to negative infinity and you get negative infinity. *)
  | finite a, finite b => finite (a + b)
  end.

Notation "x <+> y" := (RLB_plus x y) (at level 50, left associativity).

Lemma RLB_plus_comm : forall x y : RLB, x <+> y = y <+> x.
Proof.
  intros x y; destruct x, y; simpl; try reflexivity.
  - f_equal; apply Rplus_comm.
Qed.

Lemma RLB_plus_assoc : forall x y z : RLB, x <+> (y <+> z) = (x <+> y) <+> z.
Proof.
  intros x y z; destruct x, y, z; simpl; try reflexivity.
  - f_equal; rewrite Rplus_assoc; reflexivity.
Qed.

Lemma RLB_plus_left_id : forall x : RLB, finite 0 <+> x = x.
Proof.
  intro x.
  unfold RLB_plus.
  induction x.
    - f_equal.
      ring.
    - reflexivity.
Qed.

Lemma RLB_plus_right_id : forall x : RLB, x <+> finite 0 = x.
Proof.
  intro x.
  unfold RLB_plus.
  induction x.
    - f_equal.
      ring.
    - reflexivity.
Qed.
(* End RLB_plus. *)

(* Section RLB_nonNegPlus. *)
(* Refs:
 - RLB_nonNegPlus
 - RLB_nonNegSum
 - RLB_nonNegPlusEitherPlusOr0
 - RLB_nonNegPlusNotNegInf
 - horners_rule -> (* Refs: NONE *)
 - form6
 - form7
*)
Definition RLB_nonNegPlus (x y : RLB) : RLB :=
  if RLB_le_dec (finite 0) (RLB_plus x y) then RLB_plus x y else finite 0.
  
Notation "x <#> y" := (RLB_nonNegPlus x y) (at level 50, left associativity).

Lemma RLB_nonNegPlus_comm : forall x y : RLB, x <#> y = y <#> x.
Proof.
  intros x y; destruct x, y; simpl; try reflexivity.
  - unfold RLB_nonNegPlus.
    simpl.
    destruct (RLB_le_dec (finite 0) (finite (r + r0))), (RLB_le_dec (finite 0) (finite (r0 + r))).
    + f_equal.
      apply Rplus_comm.
    + exfalso.
      rewrite Rplus_comm in n.
      contradiction.
    + exfalso.
      rewrite Rplus_comm in n.
      contradiction.
    + reflexivity.
Qed.

Lemma RLB_nonNegPlus_assoc_false : exists x y z : RLB, ~(x <#> (y <#> z) = (x <#> y) <#> z).
Proof.
  pose (x := finite (-1)).
  pose (y := finite 0).
  pose (z := finite 1).
  exists x, y, z.

  (* Unfold RLB_nonNegPlus and check the equality *)
  unfold RLB_nonNegPlus at 2 4.

  (* Case analysis on the conditions *)
  simpl.
  destruct (RLB_le_dec (finite 0) (finite (0 + 1))) as [Hyz | Hyz].
  destruct (RLB_le_dec (finite 0) (finite (-1 + 0))) as [Hxy | Hxy];
  destruct (RLB_le_dec (finite 0) (finite (-1 + (0 + 1)))) as [Hx_yz | Hx_yz];
  destruct (RLB_le_dec (finite 0) (finite ((-1 + 0) + 1))) as [Hx_y_z | Hx_y_z]; simpl in *;
  try lra.

  - intro.
    unfold RLB_nonNegPlus in *.
    simpl in *.
    destruct (RLB_le_dec (finite 0) (finite (-1 + (0 + 1)))) in H;
    destruct (RLB_le_dec (finite 0) (finite (0 + 1))).
    + assert (-1 + (0 + 1) = 0).
      * lra.
      * rewrite H0 in H.
        assert ((0 + 1) = 1).
        -- lra.
        -- rewrite H1 in H.
           inversion H.
           lra.
    + apply n.
      unfold RLB_le.
      lra.
    + apply n.
      unfold RLB_le.
      lra.
    + apply n.
      unfold RLB_le.
      lra.
  - exfalso.
    apply Hyz.
    unfold RLB_le.
    lra.
Qed.

Lemma RLB_nonNegPlus_left_id_false : exists x : RLB, ~(finite 0 <#> x = x).
Proof.
  exists (finite (-1)).
  unfold RLB_nonNegPlus.
  destruct (RLB_le_dec (finite 0) (finite 0 <+> finite (-1))).
  - simpl in *.
    lra.
  - intro.
    inversion H.
    lra.
Qed.

Lemma RLB_nonNegPlus_right_id_false : exists x : RLB, ~(x <#> finite 0 = x).
Proof.
  exists (finite (-1)).
  unfold RLB_nonNegPlus.
  destruct (RLB_le_dec (finite 0) (finite (-1) <+> finite 0)).
  - simpl in *.
    lra.
  - intro.
    inversion H.
    lra.
Qed.

(* Refs:
 - horners_rule -> (* Refs: NONE *)
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Definition RLB_nonNegSum : list RLB -> RLB := fold_right RLB_nonNegPlus (finite 0).

(* Refs: NONE *)
Lemma RLB_nonNegPlusEitherPlusOr0 : forall (x y : RLB),
  x <#> y = if RLB_le_dec (finite 0) (x <+> y) then x <+> y else finite 0.
Proof.
  intros x y.
  unfold RLB_nonNegPlus.
  destruct (RLB_le_dec (finite 0) (x <+> y)); reflexivity.
Qed.

(* Refs:
 - MaxNonNegSumInits_mor -> (* Refs: horners_rule -> (* Refs: NONE *) *)
*)
Lemma RLB_nonNegPlusNotNegInf : forall (x y : RLB), exists r, (x <#> y) = finite r.
Proof.
  intros x y.
  unfold RLB_nonNegPlus.
  destruct x, y.
  - (* Case: x = finite r, y = finite r0 *)
    destruct (RLB_le_dec (finite 0) (finite r <+> finite r0)).
    + exists (r + r0). simpl. reflexivity.
    + exists 0. reflexivity.
  - (* Case: x = finite r, y = neg_inf *)
    simpl. destruct (RLB_le_dec (finite 0) neg_inf).
    + (* This case is impossible since neg_inf is not >= finite 0 *)
      exfalso. simpl in r0. exact r0.
    + exists 0. simpl. reflexivity.
  - (* Case: x = neg_inf, y = finite r *)
    simpl. destruct (RLB_le_dec (finite 0) neg_inf).
    + (* This case is impossible since neg_inf is not >= finite 0 *)
      exfalso. simpl in r0. exact r0.
    + exists 0. simpl. reflexivity.
  - (* Case: x = neg_inf, y = neg_inf *)
    simpl. destruct (RLB_le_dec (finite 0) neg_inf).
    + (* This case is impossible since neg_inf is not >= finite 0 *)
      exfalso. simpl in r. exact r.
    + exists 0. simpl. reflexivity.
Qed.

(* End RLB_nonNegPlus. *)

End RealsWithLowerBound.

Export RealsWithLowerBound.
