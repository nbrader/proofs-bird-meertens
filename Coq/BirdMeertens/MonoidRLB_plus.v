Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.RealsWithLowerBound.
Open Scope R_scope.

Require Import Coq.Arith.PeanoNat.
Require Import BirdMeertens.OptionFunctions.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import FreeMonoid.MonoidFree.
Require Import Coq.Init.Datatypes.

Require Import Coq.ssr.ssrfun.


Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

(* neg_inf takes on the role of negative infinity *)
Instance RLB_plusMagma : Magma RLB := { m_op := RLB_plus }.

Instance RLB_plusSemigroup : Semigroup RLB := { sg_assoc := RLB_plus_assoc }.

Instance RLB_plusMonoid : Monoid RLB := {
  mn_id := finite 0;
  mn_left_id := RLB_plus_left_id;
  mn_right_id := RLB_plus_right_id
}.

Module RLB_Basis.
  Definition Basis := RLB.
End RLB_Basis.

Module RLB_FreeMonoid := FreeMonoidModule RLB_Basis.

Definition identity (x : RLB) : RLB := x.
Definition RLB_sum : list RLB -> RLB := @RLB_FreeMonoid.extend _ _ _ _ RLB_FreeMonoid.FreeMonoid_UniversalProperty identity.
Definition RLB_sum_mor : MonoidHomomorphism RLB_sum := RLB_FreeMonoid.extend_monoid_homomorphism identity.
Definition RLB_sum_universal : forall (x : RLB), RLB_sum (RLB_FreeMonoid.canonical_inj x) = identity x := RLB_FreeMonoid.extend_universal identity.
Definition RLB_sum_unique (g : list RLB -> RLB) (Hg : MonoidHomomorphism g) : (forall (x : RLB), g (RLB_FreeMonoid.canonical_inj x) = identity x) -> forall a, g a = RLB_sum a := fun H => RLB_FreeMonoid.extend_unique identity g Hg H.

Definition RLB_sumImplementation : list RLB -> RLB := fun xs => fold_right RLB_plus (finite 0) xs.

Lemma RLB_plus_comm : forall i, commutative (fun (x y : RLB) => RLB_plus (RLB_plus i x) y).
Proof.
  intros.
  unfold commutative.
  intros.
  rewrite <- RLB_plus_assoc.
  rewrite (RLB_plus_comm x y).
  rewrite RLB_plus_assoc.
  reflexivity.
Qed.

Lemma RLB_sumImplementation_mor : @MonoidHomomorphism (list RLB) RLB _ _ RLB_FreeMonoid.FreeMonoid_Monoid _ _ _ RLB_sumImplementation.
Proof.
  unfold RLB_sumImplementation.
  split.

  - (* Preserving Operation *)
    intros xs ys. unfold RLB_sumImplementation.
    induction xs as [| x xs' IHxs'].
    + unfold m_op.
      unfold RLB_FreeMonoid.FreeMonoid_Magma.
      rewrite fold_right_nil.
      rewrite RLB_plus_left_id.
      rewrite app_nil_l.
      reflexivity.
    + unfold m_op in *. (* After proving this A way, make version of the proof where only the RHS of the goal equation changes each time. *)
      unfold RLB_FreeMonoid.FreeMonoid_Magma in *.
      unfold RLB_plusMagma in *.
      simpl.
      rewrite IHxs'.
      rewrite RLB_plus_assoc.
      reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma RLB_sumImplementation_universal : forall (x : RLB), RLB_sumImplementation (RLB_FreeMonoid.canonical_inj x) = identity x.
Proof.
  intros.
  simpl.
  rewrite RLB_plus_right_id.
  reflexivity.
Qed.

Lemma RLB_sum_implementation_correctness : RLB_sumImplementation = RLB_sum.
Proof.
  apply functional_extensionality.
  intros.
  apply RLB_sum_unique.
  - apply RLB_sumImplementation_mor.
  - apply RLB_sumImplementation_universal.
Qed.

Notation "x <+> y" := (RLB_plus x y) (at level 50, left associativity).

Lemma RLB_sum_distr (xs ys : list RLB) : RLB_sum (xs ++ ys) = (RLB_sum xs) <+> (RLB_sum ys).
Proof.
  apply RLB_sum_mor.
Qed.

Lemma RLB_sum_idempotent (xs : list RLB) : RLB_sum xs = RLB_sum (RLB_sum xs :: nil).
Proof.
  unfold RLB_sum.
  simpl.
  rewrite RLB_plus_right_id.
  reflexivity.
Qed.
