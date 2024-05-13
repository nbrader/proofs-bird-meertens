Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

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

(* I decided not to define RLBmaximum like they did in the original Bird Meertens Wikipedia article, because it creates the following complication:*)
(* Definition RLBmaximum : list R -> R := fun xs => match xs with
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
   None takes on this role of negative infinity. This should make the proof simpler and the result more general. *)

(* None takes on the role of negative infinity *)
Instance RLBmaxMagma : Magma RLB := { m_op := RLBmax }.

Instance RLBmaxSemigroup : Semigroup RLB := { sg_assoc := RLBmax_assoc }.

Instance RLBmaxMonoid : Monoid RLB := {
  mn_id := None;
  mn_left_id := RLBmax_left_id;
  mn_right_id := RLBmax_right_id
}.

Module RLBBasis.
  Definition Basis := RLB.
End RLBBasis.

Module RLBFreeMonoid := FreeMonoidModule RLBBasis.

Definition identity (x : RLB) : RLB := x.
Definition RLBmaximum : list RLB -> RLB := @RLBFreeMonoid.extend _ _ _ _ RLBFreeMonoid.FreeMonoid_UniversalProperty identity.
Definition RLBmaximum_mor : MonoidHomomorphism RLBmaximum := RLBFreeMonoid.extend_monoid_homomorphism identity.
Definition RLBmaximum_universal : forall (x : RLB), RLBmaximum (RLBFreeMonoid.canonical_inj x) = identity x := RLBFreeMonoid.extend_universal identity.
Definition RLBmaximum_unique (g : list RLB -> RLB) (Hg : MonoidHomomorphism g) : (forall (x : RLB), g (RLBFreeMonoid.canonical_inj x) = identity x) -> forall a, g a = RLBmaximum a := fun H => RLBFreeMonoid.extend_unique identity g Hg H.

Definition RLBmaximumImplementation : list RLB -> RLB := fun xs => fold_right RLBmax None xs.

Lemma g_comm : forall i, commutative (fun (x y : RLB) => RLBmax (RLBmax i x) y).
Proof.
  intros.
  unfold commutative.
  intros.
  rewrite <- RLBmax_assoc.
  rewrite (RLBmax_comm x y).
  rewrite RLBmax_assoc.
  reflexivity.
Qed.

Lemma g_mor : @MonoidHomomorphism (list RLB) RLB _ _ RLBFreeMonoid.FreeMonoid_Monoid _ _ _ RLBmaximumImplementation.
Proof.
  unfold RLBmaximumImplementation.
  split.

  - (* Preserving Operation *)
    intros xs ys. unfold RLBmaximumImplementation.
    induction xs as [| x xs' IHxs'].
    + unfold m_op.
      unfold RLBFreeMonoid.FreeMonoid_Magma.
      rewrite fold_right_nil.
      rewrite RLBmax_left_id.
      rewrite app_nil_l.
      reflexivity.
    + unfold m_op in *. (* After proving this A way, make version of the proof where only the RHS of the goal equation changes each time. *)
      unfold RLBFreeMonoid.FreeMonoid_Magma in *.
      unfold RLBmaxMagma in *.
      simpl.
      rewrite IHxs'.
      rewrite RLBmax_assoc.
      reflexivity.
  - simpl.
    reflexivity.
Qed.

Notation "x <|> y" := (RLBmax x y) (at level 50, left associativity).

Lemma RLBmaximum_distr (xs ys : list RLB) : RLBmaximum (xs ++ ys) = (RLBmaximum xs) <|> (RLBmaximum ys).
Proof.
  apply RLBmaximum_mor.
Qed.

Lemma RLBmaximum_idempotent (xs : list RLB) : RLBmaximum xs = RLBmaximum (RLBmaximum xs :: nil).
Proof.
  unfold RLBmaximum.
  simpl.
  rewrite RLBmax_right_id.
  reflexivity.
Qed.
