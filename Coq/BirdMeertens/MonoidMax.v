Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Open Scope R_scope.

Require Import BirdMeertens.ListFunctions.

Lemma Rmax_assoc : forall (x y z : R), Rmax x (Rmax y z) = Rmax (Rmax x y) z.
Proof.
  intros x y z.
  unfold Rmax.
  destruct (Rle_dec x (Rmax y z)) eqn:Hxyz.
  - destruct (Rle_dec y z) eqn:Hyz.
    + (* Case x ≤ z ∧ y ≤ z *)
      simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r2).
              apply r0.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r1).
              apply r0.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
    + simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           reflexivity.
        -- assert (~ x <= z).
           ++ intro.
              assert (z < y).
              ** apply Rnot_le_lt.
                 apply n.
              ** assert (y < x).
                 --- apply Rnot_le_lt.
                     apply n0.
                 --- assert (z < x).
                     +++ apply (Rlt_trans z y x H0 H1).
                     +++ apply Rlt_not_le in H2.
                         contradiction.
          ++ destruct (Rle_dec x z) as [Htrue|Hfalse].
             +++ contradiction.
             +++ reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- destruct (Rle_dec y z).
           ++ contradiction.
           ++ reflexivity.
        -- destruct (Rle_dec x z).
          --- assert (~ x <= z).
            +++ intro.
                assert (z < y).
                *** apply Rnot_le_lt.
                  apply n.
                *** assert (y < x).
                  ---- apply Rnot_le_lt.
                      apply n1.
                  ---- assert (z < x).
                      ++++ apply (Rlt_trans z y x H0 H1).
                      ++++ apply Rlt_not_le in H2.
                          contradiction.
            +++ contradiction.
          --- reflexivity.
  - destruct (Rle_dec y z) eqn:Hyz.
    + (* Case x ≤ z ∧ y ≤ z *)
      simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r1).
              apply r.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           assert (x <= z).
           ++ apply (Rle_trans x y z r0).
              apply r.
           ++ simpl.
              destruct (Rle_dec x z) as [Htrue|Hfalse].
              ** (* Case where x <= z *)
                reflexivity.
              ** (* Case where x > z, which should be impossible given hypothesis H *)
                exfalso.
                apply Hfalse.
                exact H.
        -- reflexivity.
    + simpl.
      destruct (Rle_dec (Rmax x y) z) eqn:Hxyz'.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- rewrite Hyz.
           reflexivity.
        -- assert (~ x <= z).
           ++ intro.
              assert (z < y).
              ** apply Rnot_le_lt.
                 apply n0.
              ** assert (y < x).
                 --- apply Rnot_le_lt.
                     apply n1.
                 --- assert (z < x).
                     +++ apply (Rlt_trans z y x H0 H1).
                     +++ apply Rlt_not_le in H2.
                         contradiction.
          ++ destruct (Rle_dec x z) as [Htrue|Hfalse].
             +++ contradiction.
             +++ reflexivity.
      * destruct (Rle_dec x y) eqn:Hxy.
        -- destruct (Rle_dec y z).
           ++ contradiction.
           ++ reflexivity.
        -- destruct (Rle_dec x z).
          --- assert (~ x <= z).
            +++ intro.
                assert (z < y).
                *** apply Rnot_le_lt.
                  apply n0.
                *** assert (y < x).
                  ---- apply Rnot_le_lt.
                      apply n2.
                  ---- assert (z < x).
                      ++++ apply (Rlt_trans z y x H0 H1).
                      ++++ apply Rlt_not_le in H2.
                          contradiction.
            +++ contradiction.
          --- reflexivity.
Qed.

Require Import Coq.Arith.PeanoNat.
Require Import BirdMeertens.OptionFunctions.
Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.MonoidHom.
Require Import FreeMonoid.MonoidFree.
Require Import Coq.Init.Datatypes.

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
Definition RmaxWithNegInf := liftOptionOpWithNoneID Rmax.

Instance MaxMagma : Magma (option R) := { m_op := RmaxWithNegInf }.

Lemma RmaxWithNegInf_assoc : forall x y z : (option R), RmaxWithNegInf x (RmaxWithNegInf y z) = RmaxWithNegInf (RmaxWithNegInf x y) z.
Proof.
  intros x y z.
  unfold RmaxWithNegInf.
  induction x, y, z; simpl; f_equal; apply Rmax_assoc.
Qed.

Instance MaxSemigroup : Semigroup (option R) := { sg_assoc := RmaxWithNegInf_assoc }.

Lemma RmaxWithNegInf_left_id : forall x : (option R), RmaxWithNegInf None x = x.
Proof.
  intro x.
  unfold RmaxWithNegInf.
  induction x; simpl; reflexivity.
Qed.

Lemma RmaxWithNegInf_right_id : forall x : (option R), RmaxWithNegInf x None = x.
Proof.
  intro x.
  unfold RmaxWithNegInf.
  induction x; simpl; reflexivity.
Qed.

Instance MaxMonoid : Monoid (option R) := {
  mn_id := None;
  mn_left_id := RmaxWithNegInf_left_id;
  mn_right_id := RmaxWithNegInf_right_id
}.

Require Import Coq.ssr.ssrfun.
Lemma RmaxWithNegInf_comm : commutative RmaxWithNegInf.
Proof.

Admitted.

Module RBasis.
  Definition Basis := option R.
End RBasis.

Module RFreeMonoid := FreeMonoidModule RBasis.

Definition identity (x : option R) : option R := x.
Definition maximum : list (option R) -> option R := @RFreeMonoid.extend _ _ _ _ RFreeMonoid.FreeMonoid_UniversalProperty identity.
Definition maximum_mor : MonoidHomomorphism maximum := RFreeMonoid.extend_monoid_homomorphism identity.
Definition maximum_universal : forall (x : option R), maximum (RFreeMonoid.canonical_inj x) = identity x := RFreeMonoid.extend_universal identity.
Definition maximum_unique (g : list (option R) -> option R) (Hg : MonoidHomomorphism g) : (forall (x : option R), g (RFreeMonoid.canonical_inj x) = identity x) -> forall a, g a = maximum a := fun H => RFreeMonoid.extend_unique identity g Hg H.

Definition maximumImplementation : list (option R) -> option R := fun xs => fold_right RmaxWithNegInf None xs.


Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.

Lemma g_comm : forall i, commutative (fun (x y : option R) => RmaxWithNegInf (RmaxWithNegInf i x) y).
Proof.

Admitted.

Lemma g_mor : @MonoidHomomorphism (list (option R)) (option R) _ _ RFreeMonoid.FreeMonoid_Monoid _ _ _ maximumImplementation.
Proof.
  unfold maximumImplementation.
  split.

  - (* Preserving Operation *)
    intros xs ys. unfold maximumImplementation.
    induction xs as [| x xs' IHxs'].
    + unfold m_op.
      unfold RFreeMonoid.FreeMonoid_Magma.
      rewrite fold_right_nil.
      rewrite RmaxWithNegInf_left_id.
      rewrite app_nil_l.
      reflexivity.
    + unfold m_op in *. (* After proving this A way, make version of the proof where only the RHS of the goal equation changes each time. *)
      unfold RFreeMonoid.FreeMonoid_Magma in *.
      unfold MaxMagma in *.
      simpl.
      rewrite IHxs'.
      rewrite RmaxWithNegInf_assoc.
      reflexivity.
  - simpl.
    reflexivity.
Qed.

Definition RplusWithNegInf : option R -> option R -> option R := liftOption2 (fun x y => x + y).

Definition RsumWithNegInf : list (option R) -> option R := fun xs => fold_right RplusWithNegInf None xs.

(* x <#> y = (x + y) <|> 0 *)
(* This might not be necessary anymore with the use of a the negative infinity to give an actual monoid *)
Definition RnonzeroSumWithNegInf : option R -> option R -> option R := fun mx my => RmaxWithNegInf (RplusWithNegInf mx my) (Some 0).

(* (u,v) <.> x = let w = (v+x) <|> 0 in (u <|> w, w) *)
Definition RmaxWithNegInfSoFarAndPreviousNonzeroSum : option R -> (option R * option R) -> (option R * option R) := fun x uv => match uv with
  | (u, v) => let w := RnonzeroSumWithNegInf v x in (RmaxWithNegInf u w, w)
end.

Notation "x <+> y" := (RplusWithNegInf x y) (at level 50, left associativity).
Notation "x <|> y" := (RmaxWithNegInf x y) (at level 50, left associativity).
Notation "x <#> y" := (RnonzeroSumWithNegInf x y) (at level 50, left associativity).
Notation "x <.> y" := (RmaxWithNegInfSoFarAndPreviousNonzeroSum x y) (at level 50, left associativity).

Lemma maximum_distr (xs ys : list (option R)) : maximum (xs ++ ys) = (maximum xs) <|> (maximum ys).
Proof.
  apply maximum_mor.
Qed.

Lemma maximum_idempotent (xs : list (option R)) : maximum xs = maximum (maximum xs :: nil).
Proof.
  pose (g xs := fold_right RmaxWithNegInf None xs).
  assert (g_mor : @MonoidHomomorphism (list (option R)) (option R) _ _ RFreeMonoid.FreeMonoid_Monoid _ _ _ g).
  (* - apply (RFreeMonoid.extend_mor).
  assert (g_universal : forall (x : option R), g (RFreeMonoid.canonical_inj x).
  - 
  assert (maximum = fun xs => foldl RmaxWithNegInf None xs).
  - apply (maximum_unique ).
  unfold RFreeMonoid.extend.
  destruct extend. *)
Admitted.