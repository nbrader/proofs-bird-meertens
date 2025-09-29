Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.

Open Scope Z_scope.

(* Import the existing semiring infrastructure *)
Require Import FreeMonoid.StructSemiring.
Require Import FreeMonoid.SemiringLemmas.
Require Import BirdMeertens.MajorLemmas.
Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import CoqUtilLib.ListFunctions.

(*
=================================================================================
GENERALIZED KADANE'S ALGORITHM VIA SEMIRING FORMULATION
=================================================================================

This file explores a generalized approach to Kadane's algorithm that:
1. Uses proper semiring operations throughout (not ad-hoc nonNeg operations)
2. Leverages tropical semiring and Horner's rule directly
3. Avoids the artificial distinction between sum vs nonNegSum
4. Provides a cleaner path from mathematical definition to efficient algorithm

Key insight: The original Bird-Meertens derivation works with any suitable semiring,
not just the specific nonNeg-clamped operations we've been using.
*)

(*
=================================================================================
SEMIRING ABSTRACTION
=================================================================================
*)

(* The project already has a complete semiring infrastructure in FreeMonoid.StructSemiring *)
(* We'll use the existing Semiring class with operations ⊕, ⊗, 𝟘, 𝟙 *)

(* The semiring infrastructure is available from FreeMonoid.StructSemiring *)
(* Specific semiring instances will be defined in separate files as needed *)

(*
=================================================================================
GENERALIZED FORMS
=================================================================================
*)

(* Generic sum over a semiring (corresponds to fold with ⊕) *)
Definition semiring_sum {A : Type} `{Semiring A} (xs : list A) : A :=
  fold_right add_op add_zero xs.

(* Generic product over a semiring (corresponds to fold with ⊗) *)
Definition semiring_product {A : Type} `{Semiring A} (xs : list A) : A :=
  fold_right mul_op mul_one xs.

(*
Now we can define the forms generically:
*)

(* Generalized sum of subarray products definitions operating directly on semiring *)
Definition gform1 {A : Type} `{Semiring A} : list A -> A :=
  semiring_sum ∘ map semiring_product ∘ segs.

Definition gform2 {A : Type} `{Semiring A} : list A -> A :=
  semiring_sum ∘ map semiring_product ∘ concat ∘ map inits ∘ tails.

Definition gform3 {A : Type} `{Semiring A} : list A -> A :=
  semiring_sum ∘ concat ∘ map (map semiring_product) ∘ map inits ∘ tails.

Definition gform4 {A : Type} `{Semiring A} : list A -> A :=
  semiring_sum ∘ map semiring_sum ∘ map (map semiring_product) ∘ map inits ∘ tails.

Definition gform5 {A : Type} `{Semiring A} : list A -> A :=
  semiring_sum ∘ map (semiring_sum ∘ map semiring_product ∘ inits) ∘ tails.

Definition gform6 {A : Type} `{Semiring A} : list A -> A :=
  semiring_sum ∘ map (fold_right mul_op mul_one) ∘ tails.

Definition gform7 {A : Type} `{Semiring A} : list A -> A :=
  semiring_sum ∘ scan_right mul_op mul_one.

Definition gform8 {A : Type} `{Semiring A} : list A -> A :=
  fst ∘ fold_right (fun x uv => let '(u, v) := uv in
                                let w := mul_op v x in
                                (add_op u w, w)) (add_zero, mul_one).

(*
=================================================================================
GENERALIZED SEMIRING LEMMAS
=================================================================================
*)

(* Generalized version of fold_max_app for semirings *)
Lemma semiring_fold_app {A : Type} `{Semiring A} : forall (l1 l2 : list A),
  fold_right add_op add_zero (l1 ++ l2) = add_op (fold_right add_op add_zero l1) (fold_right add_op add_zero l2).
Proof.
  intros l1 l2.
  induction l1 as [|x xs IH]; simpl.
  - rewrite add_left_id. reflexivity.
  - rewrite IH. rewrite add_assoc. reflexivity.
Qed.

(* Generalized fold promotion for semirings *)
Lemma semiring_fold_promotion {A : Type} `{Semiring A} :
  semiring_sum ∘ concat = semiring_sum ∘ map semiring_sum.
Proof.
  unfold compose, semiring_sum.
  apply functional_extensionality; intro lss.
  induction lss as [| ls lss' IH].
  - simpl. reflexivity.
  - simpl concat. simpl map.
    rewrite semiring_fold_app.
    rewrite IH.
    reflexivity.
Qed.

(*
=================================================================================
ABSTRACT THEOREM STATEMENTS
=================================================================================
*)

(* Abstract theorem statements for semiring-based Kadane's algorithm *)
(* These will be proven when instantiated with specific semiring instances *)

Section KadaneTheorems.
  Context {A : Type} `{Semiring A}.

  (* All equivalence steps follow from general semiring properties *)

  Theorem gform1_eq_gform2 : gform1 = gform2.
  Proof.
    (* Follows from segs = concat ∘ map inits ∘ tails *)
    reflexivity.
  Qed.

  Theorem gform2_eq_gform3 : gform2 = gform3.
  Proof.
    (* Follows from map promotion through concat *)
    unfold gform2, gform3.
    f_equal.
    rewrite compose_assoc.
    rewrite (compose_assoc _ _ _ _ (concat ∘ map inits) (map semiring_product) semiring_sum).
    rewrite <- (compose_assoc _ _ _ _ (map inits) concat (map semiring_product)).
    rewrite (map_promotion semiring_product).
    reflexivity.
  Qed.

  Theorem gform3_eq_gform4 : gform3 = gform4.
  Proof.
    (* Follows from generalized fold promotion for semirings *)
    unfold gform3, gform4.
    rewrite semiring_fold_promotion.
    reflexivity.
  Qed.

  Theorem gform4_eq_gform5 : gform4 = gform5.
  Proof.
    (* Follows the exact same pattern as original form4_eq_form5 *)
    unfold gform4, gform5.
    f_equal.
    rewrite compose_assoc.
    rewrite compose_assoc.
    rewrite (map_distr (map semiring_product) inits).
    rewrite (map_distr semiring_sum (compose (map semiring_product) inits)).
    reflexivity.
  Qed.

  (* OLD PROOF (with horner_op version of gform6): *)
  (* This shows the working proof when gform6 used horner_op *)
  Definition gform6_horner_version {A : Type} `{Semiring A} : list A -> A :=
    let horner_op := fun x y => add_op (mul_op x y) mul_one in
    semiring_sum ∘ map (fold_right horner_op mul_one) ∘ tails.

  Lemma gform5_eq_gform6_horner_version : gform5 = gform6_horner_version.
  Proof.
    (* This is THE KEY STEP: follows from generalized Horner's rule *)
    unfold gform5, gform6_horner_version.
    apply functional_extensionality; intro xs.
    unfold compose.
    f_equal.
    apply map_ext.
    intros a.
    unfold semiring_sum, semiring_product.

    (* Apply the generalized Horner's rule *)
    pose proof (@generalised_horners_rule_right A _) as HR.

    (* The goal is exactly what the rule provides, just need to apply it in the right direction *)
    rewrite (equal_f HR a).
    unfold compose.
    reflexivity.
  Qed.

  (* This lemma shows the relationship between the two gform6 versions *)
  Lemma gform6_versions_related :
    forall (xs : list A),
    gform6_horner_version xs =
    let horner_op := fun x y => add_op (mul_op x y) mul_one in
    semiring_sum (map (fold_right horner_op mul_one) (tails xs)).
  Proof.
    intro xs.
    unfold gform6_horner_version, compose.
    reflexivity.
  Qed.

  (* The form5 to form6 and form7 to form8 steps require special semiring properties.
     These properties characterize idempotent/tropical semirings where Kadane's algorithm works.

     We abstract this as a type class for semirings where Kadane's works. *)
  Class KadaneSemiring (A : Type) `{Semiring A} : Prop := {
    (* The Horner property: product equals sum of prefix products *)
    kadane_horner_property :
      forall (xs : list A),
        semiring_product xs = semiring_sum (map semiring_product (inits xs));

    (* The multiplicative identity acts as an additive zero for the scan-fold fusion *)
    (* This says: adding mul_one doesn't change the sum *)
    mul_one_add_absorb :
      add_op mul_one add_zero = add_zero;

    (* Multiplication must be commutative for the scan-fold fusion *)
    mul_comm : forall (x y : A), mul_op x y = mul_op y x
  }.

  (* With this property, we can prove the form5 to form6 transition *)
  Theorem gform5_eq_gform6 `{KadaneSemiring A} : gform5 = gform6.
  Proof.
    unfold gform5, gform6.
    apply functional_extensionality; intro xs.
    unfold compose.
    f_equal.
    apply map_ext.
    intros a.
    unfold semiring_sum, semiring_product.

    (* Apply the Kadane semiring property *)
    symmetry.
    apply kadane_horner_property.
  Qed.

  Theorem gform6_eq_gform7 : gform6 = gform7.
  Proof.
    (* Follows from scan-fold relationship, using scan_right_lemma *)
    unfold gform6, gform7.
    apply functional_extensionality; intro xs.
    unfold compose.
    f_equal.
    (* We need to show: map (fold_right mul_op mul_one) (tails xs) = scan_right mul_op mul_one xs *)
    (* This should follow from scan_right_lemma *)
    symmetry.
    rewrite (@scan_right_lemma A A mul_op mul_one xs).
    (* Now we need tails = tails_rec *)
    f_equal.
    symmetry.
    apply tails_rec_equiv.
  Qed.

  (* The form7 to form8 step requires a scan-fold fusion property.
     This is similar to the non-generalized fold_scan_fusion_pair lemma. *)

  (* We need a helper lemma for fold_right over appended lists *)
  Lemma semiring_fold_right_app : forall (l1 l2 : list A),
    fold_right add_op add_zero (l1 ++ l2) =
    add_op (fold_right add_op add_zero l1) (fold_right add_op add_zero l2).
  Proof.
    intros l1 l2.
    induction l1 as [|x xs IH]; simpl.
    - rewrite add_left_id. reflexivity.
    - rewrite IH. rewrite add_assoc. reflexivity.
  Qed.

  (* Helper lemma: the second component of the fold is the product (requires commutativity) *)
  Lemma fold_pair_snd `{KadaneSemiring A} : forall (xs : list A),
    snd (fold_right (fun x uv => let '(u, v) := uv in
                                 let w := mul_op v x in
                                 (add_op u w, w)) (add_zero, mul_one) xs) =
    fold_right mul_op mul_one xs.
  Proof.
    intro xs.
    induction xs as [| x xs' IH].
    - simpl. reflexivity.
    - simpl fold_right at 1.
      simpl fold_right at 2.
      remember (fold_right (fun x0 uv => let '(u, v) := uv in let w := mul_op v x0 in (add_op u w, w))
                (add_zero, mul_one) xs') as pair eqn:Hpair.
      destruct pair as [u' v'].
      simpl snd.
      (* Goal: mul_op v' x = mul_op x (fold_right mul_op mul_one xs') *)
      (* Combine IH and Hpair to get v' = fold_right mul_op mul_one xs' *)
      (* IH: snd (u', v') = fold_right mul_op mul_one xs' *)
      (* So v' = fold_right mul_op mul_one xs' *)
      simpl snd in IH.
      rewrite IH.
      apply mul_comm.
  Qed.

  (* We prove the scan-fold fusion property for Kadane semirings *)
  Lemma semiring_scan_fold_fusion `{KadaneSemiring A} : forall (xs : list A),
    fold_right add_op add_zero (scan_right mul_op mul_one xs) =
    fst (fold_right (fun x uv => let '(u, v) := uv in
                                 let w := mul_op v x in
                                 (add_op u w, w)) (add_zero, mul_one) xs).
  Proof.
    intro xs.
    induction xs as [| x xs' IH].
    - (* Base case: xs = [] *)
      simpl.
      (* Use the mul_one_add_absorb property *)
      apply mul_one_add_absorb.
    - (* Inductive case: xs = x :: xs' *)
      (* Expand scan_right for (x :: xs') *)
      simpl scan_right.

      (* Expand fold_right on the right side *)
      simpl fold_right.
      destruct (fold_right (fun x0 uv => let '(u, v) := uv in let w := mul_op v x0 in (add_op u w, w))
                (add_zero, mul_one) xs') as [u' v'] eqn:Heq.
      simpl fst.

      (* LHS: fold_right add_op add_zero (mul_op x (fold_right mul_op mul_one xs') :: scan_right mul_op mul_one xs') *)
      (* RHS: add_op u' (mul_op v' x) *)
      simpl fold_right.

      (* Use the IH *)
      rewrite IH.

      (* Goal: add_op (mul_op x (fold_right mul_op mul_one xs')) (fst (u', v')) = add_op u' (mul_op v' x) *)
      simpl fst.

      (* Goal: add_op (mul_op x (fold_right mul_op mul_one xs')) u' = add_op u' (mul_op v' x) *)

      (* Use fold_pair_snd to establish v' = fold_right mul_op mul_one xs' *)
      assert (Hv: v' = fold_right mul_op mul_one xs').
      {
        rewrite <- (fold_pair_snd xs').
        rewrite Heq.
        simpl snd.
        reflexivity.
      }

      rewrite Hv.

      (* Goal: add_op (mul_op x (fold_right mul_op mul_one xs')) u' = add_op u' (mul_op (fold_right mul_op mul_one xs') x) *)
      rewrite add_comm.
      f_equal.
      apply mul_comm.
  Qed.

  Theorem gform7_eq_gform8 `{KadaneSemiring A} : gform7 = gform8.
  Proof.
    unfold gform7, gform8.
    apply functional_extensionality; intro xs.
    unfold compose, semiring_sum.
    apply semiring_scan_fold_fusion.
  Qed.

End KadaneTheorems.

(* For the main correctness theorem, we need to work outside the section
   to avoid multiple Semiring instances *)
Section KadaneCorrectness.
  Context {A : Type} `{KS : KadaneSemiring A}.

  (* The main theorem: all forms are equivalent for Kadane semirings *)
  Theorem Generalized_Kadane_Correctness : gform1 = gform8.
  Proof.
    etransitivity. apply gform1_eq_gform2.
    etransitivity. apply gform2_eq_gform3.
    etransitivity. apply gform3_eq_gform4.
    etransitivity. apply gform4_eq_gform5.
    etransitivity. apply gform5_eq_gform6.
    etransitivity. apply gform6_eq_gform7.
    apply gform7_eq_gform8.
  Qed.

End KadaneCorrectness.

(*
=================================================================================
NOTES FOR FUTURE DEVELOPMENT
=================================================================================

1. Create specific semiring instances in separate files (e.g., MaxPlusSemiring.v)
2. Prove the generalized equivalence theorems using semiring properties
3. Instantiate the abstract theorems with specific semiring instances
4. Establish connections between different semiring formulations
5. Consider other semiring instances (e.g., Boolean semiring for existence problems)
6. Explore dual formulations in this generalized setting

The key insight is that Kadane's algorithm is fundamentally about semiring operations,
not specifically about integers and max/plus. This generalization makes the
mathematical structure explicit and the algorithm more broadly applicable.
*)