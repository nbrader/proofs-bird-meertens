Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.RealsWithLowerBound.
Open Scope R_scope.

Require Import Coq.Arith.PeanoNat.
Require Import BirdMeertens.OptionFunctions.
Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import FreeMonoid.MonoidFree.
Require Import Coq.Init.Datatypes.

Require Import Coq.ssr.ssrfun.


Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

(* I decided not to define RLB_maximum like they did in the original Bird Meertens Wikipedia article, because it creates the following complication:*)
(* Definition RLB_maximum : list R -> R := fun xs => match xs with
  | [] => 0 (* This would be incorrect for lists of negatives but:
                1) We consider only lists of at least 1 positive and 1 negative because alternatives are trivial:
                    - Lists without negatives have a MaxSegSum equal to the sum of the list
                    - Lists without positives have a MaxSegSum equal to the least negative member
                    To Do: Make this explicit in a more general MaxSegSum function which covers these other cases as described above.
                2) segs, inits and scanl don't map to the empty list and the only way to get the empty list
                      from map and concat is from the empty list and a list of empty lists respectively so nothing
                      we can get from proceeding functions in the forms below will trigger this case anyway. *)
  | x' :: xs' => foldl Rmax 0 xs.
end. *)

(* Instead, I'm just extending Rmax to a monoid with the inclusion of a "negative infinity" element which will act as identity element.
   neg_inf takes on this role of negative infinity. This should make the proof simpler and the result more general. *)

(* neg_inf takes on the role of negative infinity *)
Instance RLB_maxMagma : Magma RLB := { m_op := RLB_max }.

Instance RLB_maxSemigroup : Semigroup RLB := { sg_assoc := RLB_max_assoc }.

Instance RLB_maxMonoid : Monoid RLB := {
  mn_id := neg_inf;
  mn_left_id := RLB_max_left_id;
  mn_right_id := RLB_max_right_id
}.

Module RLB_Basis.
  Definition Basis := RLB.
End RLB_Basis.

Module RLB_FreeMonoid := FreeMonoidModule RLB_Basis.

Definition identity (x : RLB) : RLB := x.
Definition RLB_maximum : list RLB -> RLB := @RLB_FreeMonoid.extend _ _ _ _ RLB_FreeMonoid.FreeMonoid_UniversalProperty identity.
Definition RLB_maximum_mor : MonoidHomomorphism RLB_maximum := RLB_FreeMonoid.extend_monoid_homomorphism identity.
Definition RLB_maximum_universal : forall (x : RLB), RLB_maximum (RLB_FreeMonoid.canonical_inj x) = identity x := RLB_FreeMonoid.extend_universal identity.
Definition RLB_maximum_unique (g : list RLB -> RLB) (Hg : MonoidHomomorphism g) : (forall (x : RLB), g (RLB_FreeMonoid.canonical_inj x) = identity x) -> forall a, g a = RLB_maximum a := fun H => RLB_FreeMonoid.extend_unique identity g Hg H.

Definition RLB_maximumImplementation : list RLB -> RLB := fun xs => fold_right RLB_max neg_inf xs.

Lemma g_comm : forall i, commutative (fun (x y : RLB) => RLB_max (RLB_max i x) y).
Proof.
  intros.
  unfold commutative.
  intros.
  rewrite <- RLB_max_assoc.
  rewrite (RLB_max_comm x y).
  rewrite RLB_max_assoc.
  reflexivity.
Qed.

Lemma g_mor : @MonoidHomomorphism (list RLB) RLB _ _ RLB_FreeMonoid.FreeMonoid_Monoid _ _ _ RLB_maximumImplementation.
Proof.
  unfold RLB_maximumImplementation.
  split.

  - (* Preserving Operation *)
    intros xs ys. unfold RLB_maximumImplementation.
    induction xs as [| x xs' IHxs'].
    + unfold m_op.
      unfold RLB_FreeMonoid.FreeMonoid_Magma.
      rewrite fold_right_nil.
      rewrite RLB_max_left_id.
      rewrite app_nil_l.
      reflexivity.
    + unfold m_op in *. (* After proving this A way, make version of the proof where only the RHS of the goal equation changes each time. *)
      unfold RLB_FreeMonoid.FreeMonoid_Magma in *.
      unfold RLB_maxMagma in *.
      simpl.
      rewrite IHxs'.
      rewrite RLB_max_assoc.
      reflexivity.
  - simpl.
    reflexivity.
Qed.

Notation "x <|> y" := (RLB_max x y) (at level 50, left associativity).

Lemma RLB_maximum_distr (xs ys : list RLB) : RLB_maximum (xs ++ ys) = (RLB_maximum xs) <|> (RLB_maximum ys).
Proof.
  apply RLB_maximum_mor.
Qed.

Lemma RLB_maximum_singleton (x : RLB) : RLB_maximum [x] = x.
Proof.
  unfold RLB_maximum.
  unfold RLB_FreeMonoid.extend.
  simpl.
  apply RLB_max_right_id.
Qed.

Lemma RLB_maximum_idempotent (xs : list RLB) : RLB_maximum xs = RLB_maximum (RLB_maximum xs :: nil).
Proof.
  unfold RLB_maximum.
  simpl.
  rewrite RLB_max_right_id.
  reflexivity.
Qed.
