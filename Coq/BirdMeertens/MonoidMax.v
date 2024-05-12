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

(* I decided not to define maximum like they did in the original Bird Meertens Wikipedia article, because it creates the following complication:*)
(* Definition maximum : list R -> R := fun xs => match xs with
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
Instance MaxMagma : Magma RLB := { m_op := RLBmax }.

Instance MaxSemigroup : Semigroup RLB := { sg_assoc := RLBmax_assoc }.

Instance MaxMonoid : Monoid RLB := {
  mn_id := None;
  mn_left_id := RLBmax_left_id;
  mn_right_id := RLBmax_right_id
}.

Module RBasis.
  Definition Basis := RLB.
End RBasis.

Module RFreeMonoid := FreeMonoidModule RBasis.

Definition identity (x : RLB) : RLB := x.
Definition maximum : list RLB -> RLB := @RFreeMonoid.extend _ _ _ _ RFreeMonoid.FreeMonoid_UniversalProperty identity.
Definition maximum_mor : MonoidHomomorphism maximum := RFreeMonoid.extend_monoid_homomorphism identity.
Definition maximum_universal : forall (x : RLB), maximum (RFreeMonoid.canonical_inj x) = identity x := RFreeMonoid.extend_universal identity.
Definition maximum_unique (g : list RLB -> RLB) (Hg : MonoidHomomorphism g) : (forall (x : RLB), g (RFreeMonoid.canonical_inj x) = identity x) -> forall a, g a = maximum a := fun H => RFreeMonoid.extend_unique identity g Hg H.

Definition maximumImplementation : list RLB -> RLB := fun xs => fold_right RLBmax None xs.

Lemma g_comm : forall i, commutative (fun (x y : RLB) => RLBmax (RLBmax i x) y).
Proof.

Admitted.

Lemma g_mor : @MonoidHomomorphism (list RLB) RLB _ _ RFreeMonoid.FreeMonoid_Monoid _ _ _ maximumImplementation.
Proof.
  unfold maximumImplementation.
  split.

  - (* Preserving Operation *)
    intros xs ys. unfold maximumImplementation.
    induction xs as [| x xs' IHxs'].
    + unfold m_op.
      unfold RFreeMonoid.FreeMonoid_Magma.
      rewrite fold_right_nil.
      rewrite RLBmax_left_id.
      rewrite app_nil_l.
      reflexivity.
    + unfold m_op in *. (* After proving this A way, make version of the proof where only the RHS of the goal equation changes each time. *)
      unfold RFreeMonoid.FreeMonoid_Magma in *.
      unfold MaxMagma in *.
      simpl.
      rewrite IHxs'.
      rewrite RLBmax_assoc.
      reflexivity.
  - simpl.
    reflexivity.
Qed.

(* (u,v) <.> x = let w = (v+x) <|> 0 in (u <|> w, w) *)
Definition RLBmaxSoFarAndPreviousSum : RLB -> (RLB * RLB) -> (RLB * RLB) := fun x uv => match uv with
  | (u, v) => let w := RLBplus v x in (RLBmax u w, w)
end.

Notation "x <+> y" := (RLBsum x y) (at level 50, left associativity).
Notation "x <|> y" := (RLBmax x y) (at level 50, left associativity).
Notation "x <.> y" := (RLBmaxSoFarAndPreviousSum x y) (at level 50, left associativity).

Lemma maximum_distr (xs ys : list RLB) : maximum (xs ++ ys) = (maximum xs) <|> (maximum ys).
Proof.
  apply maximum_mor.
Qed.

Lemma maximum_idempotent (xs : list RLB) : maximum xs = maximum (maximum xs :: nil).
Proof.
  pose (g xs := fold_right RLBmax None xs).
  assert (g_mor : @MonoidHomomorphism (list RLB) RLB _ _ RFreeMonoid.FreeMonoid_Monoid _ _ _ g).
  (* - apply (RFreeMonoid.extend_mor).
  assert (g_universal : forall (x : RLB), g (RFreeMonoid.canonical_inj x).
  - 
  assert (maximum = fun xs => foldl RLBmax None xs).
  - apply (maximum_unique ).
  unfold RFreeMonoid.extend.
  destruct extend. *)
Admitted.