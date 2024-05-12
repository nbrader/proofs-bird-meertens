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

(* I decided not to define RLBsum like they did in the original Bird Meertens Wikipedia article, because it creates the following complication:*)
(* Definition RLBsum : list R -> R := fun xs => match xs with
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
Instance RLBplusMagma : Magma RLB := { m_op := RLBplus }.

Instance RLBplusSemigroup : Semigroup RLB := { sg_assoc := RLBplus_assoc }.

Instance RLBplusMonoid : Monoid RLB := {
  mn_id := Some 0;
  mn_left_id := RLBplus_left_id;
  mn_right_id := RLBplus_right_id
}.

Module RLBBasis.
  Definition Basis := RLB.
End RLBBasis.

Module RLBFreeMonoid := FreeMonoidModule RLBBasis.

Definition identity (x : RLB) : RLB := x.
Definition RLBsum : list RLB -> RLB := @RLBFreeMonoid.extend _ _ _ _ RLBFreeMonoid.FreeMonoid_UniversalProperty identity.
Definition RLBsum_mor : MonoidHomomorphism RLBsum := RLBFreeMonoid.extend_monoid_homomorphism identity.
Definition RLBsum_universal : forall (x : RLB), RLBsum (RLBFreeMonoid.canonical_inj x) = identity x := RLBFreeMonoid.extend_universal identity.
Definition RLBsum_unique (g : list RLB -> RLB) (Hg : MonoidHomomorphism g) : (forall (x : RLB), g (RLBFreeMonoid.canonical_inj x) = identity x) -> forall a, g a = RLBsum a := fun H => RLBFreeMonoid.extend_unique identity g Hg H.

Definition RLBsumImplementation : list RLB -> RLB := fun xs => fold_right RLBplus (Some 0) xs.

Lemma g_comm : forall i, commutative (fun (x y : RLB) => RLBplus (RLBplus i x) y).
Proof.
  intros.
  unfold commutative.
  intros.
  rewrite <- RLBplus_assoc.
  rewrite (RLBplus_comm x y).
  rewrite RLBplus_assoc.
  reflexivity.
Qed.

Lemma g_mor : @MonoidHomomorphism (list RLB) RLB _ _ RLBFreeMonoid.FreeMonoid_Monoid _ _ _ RLBsumImplementation.
Proof.
  unfold RLBsumImplementation.
  split.

  - (* Preserving Operation *)
    intros xs ys. unfold RLBsumImplementation.
    induction xs as [| x xs' IHxs'].
    + unfold m_op.
      unfold RLBFreeMonoid.FreeMonoid_Magma.
      rewrite fold_right_nil.
      rewrite RLBplus_left_id.
      rewrite app_nil_l.
      reflexivity.
    + unfold m_op in *. (* After proving this A way, make version of the proof where only the RHS of the goal equation changes each time. *)
      unfold RLBFreeMonoid.FreeMonoid_Magma in *.
      unfold RLBplusMagma in *.
      simpl.
      rewrite IHxs'.
      rewrite RLBplus_assoc.
      reflexivity.
  - simpl.
    reflexivity.
Qed.

(* (u,v) <.> x = let w = (v+x) <|> 0 in (u <|> w, w) *)
Definition RLBplusSoFarAndPreviousSum : RLB -> (RLB * RLB) -> (RLB * RLB) := fun x uv => match uv with
  | (u, v) => let w := RLBplus v x in (RLBplus u w, w)
end.

Notation "x <+> y" := (RLBplus x y) (at level 50, left associativity).
Notation "x <|> y" := (RLBplus x y) (at level 50, left associativity).
Notation "x <.> y" := (RLBplusSoFarAndPreviousSum x y) (at level 50, left associativity).

Lemma RLBsum_distr (xs ys : list RLB) : RLBsum (xs ++ ys) = (RLBsum xs) <|> (RLBsum ys).
Proof.
  apply RLBsum_mor.
Qed.

Lemma RLBsum_idempotent (xs : list RLB) : RLBsum xs = RLBsum (RLBsum xs :: nil).
Proof.
  unfold RLBsum.
  simpl.
  rewrite RLBplus_right_id.
  reflexivity.
Qed.
