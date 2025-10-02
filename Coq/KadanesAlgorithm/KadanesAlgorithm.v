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

This file provides a generalized semiring-based formulation of Kadane's algorithm.

KEY RESULTS:

Forms gform1 through gform7 work for ANY semiring (ℤ, tropical, etc.)!
- gform1-gform4: Use basic list manipulation and semiring properties
- gform5 → gform6: Uses Horner's rule (proven for all semirings)
- gform6 → gform7: Uses scan-fold relationship

See companion files:
- MaxSubarrayKadane.v: Tropical semiring case with clamping arguments for gform7→gform8
- AlternativeGform8.v: Analysis of why (add_zero, mul_one) is uniquely determined
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
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  semiring_sum ∘ map (fold_right horner_op mul_one) ∘ tails.

Definition gform7 {A : Type} `{Semiring A} : list A -> A :=
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  semiring_sum ∘ scan_right horner_op mul_one.

Definition gform8 {A : Type} `{Semiring A} : list A -> A :=
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  let pair_step := fun x (uv : A * A) =>
    let (u, v) := uv in
    let w := horner_op x v in
    (add_op w u, w)
  in
  fst ∘ fold_right pair_step (add_op mul_one add_zero, mul_one).

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

  (* The gform5 → gform6 transition follows from Horner's rule, which holds for ANY semiring *)

  Theorem gform5_eq_gform6 : gform5 = gform6.
  Proof.
    (* This is THE KEY STEP: follows from generalized Horner's rule *)
    unfold gform5, gform6.
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

  Theorem gform6_eq_gform7 : gform6 = gform7.
  Proof.
    (* Follows from scan-fold relationship, using scan_right_lemma *)
    unfold gform6, gform7.
    apply functional_extensionality; intro xs.
    unfold compose.
    f_equal.
    (* We need to show: map (fold_right horner_op mul_one) (tails xs) = scan_right horner_op mul_one xs *)
    (* This should follow from scan_right_lemma *)
    set (horner_op := fun x y => add_op (mul_op x y) mul_one).
    symmetry.
    rewrite (@scan_right_lemma A A horner_op mul_one xs).
    (* Now we need tails = tails_rec *)
    f_equal.
    symmetry.
    apply tails_rec_equiv.
  Qed.

  (*
  =================================================================================
  FOLD-SCAN FUSION LAW
  =================================================================================

  This is the maximally general fold-scan fusion law with NO assumptions on op_1.
  By using the swapped argument order in op_3, we avoid any commutativity requirement.
  *)

  (* Helper lemma: snd of fold with op_3 tracks fold with op_2 *)
  Lemma fold_pair_snd_tracks_fold :
    forall (op_1 : A -> A -> A)
      (op_2 : A -> A -> A)
      (init_a : A)
      (init_b : A)
      (xs : list A),
    let op_3 := fun x (uv : A * A) =>
      let (u, v) := uv in
      let w := op_2 x v in
      (op_1 w u, w)
    in
    snd (fold_right op_3 (init_a, init_b) xs) = fold_right op_2 init_b xs.
  Proof.
    intros op_1 op_2 init_a init_b xs op_3.
    induction xs as [|x xs' IH].
    - simpl. reflexivity.
    - simpl fold_right.
      unfold op_3 at 1.
      destruct (fold_right op_3 (init_a, init_b) xs') as [u v].
      simpl snd.
      simpl snd in IH.
      rewrite IH.
      reflexivity.
  Qed.

  Lemma fold_scan_fusion :
    forall (op_1 : A -> A -> A)
      (op_2 : A -> A -> A)
      (init_a : A)
      (init_b : A)
      (xs : list A),
    let op_3 := fun x (uv : A * A) =>
      let (u, v) := uv in
      let w := op_2 x v in
      (op_1 w u, w)
    in
    fold_right op_1 init_a (scan_right op_2 init_b xs) =
    fst (fold_right op_3 (op_1 init_b init_a, init_b) xs).
  Proof.
    intros op_1 op_2 init_a init_b xs op_3.
    induction xs as [|x xs' IH].
    - (* Base case *)
      simpl. reflexivity.
    - (* Inductive step *)
      simpl scan_right.
      simpl fold_right at 1.
      assert (Hsnd: fold_right op_2 init_b xs' =
                    snd (fold_right op_3 (op_1 init_b init_a, init_b) xs')).
      { symmetry. apply fold_pair_snd_tracks_fold. }
      rewrite Hsnd.
      rewrite IH.
      remember (fold_right op_3 (op_1 init_b init_a, init_b) xs') as pair eqn:Hpair.
      destruct pair as [u v].
      simpl fst. simpl snd.
      rewrite <- Hpair.
      unfold op_3. simpl fst.
      reflexivity.
  Qed.

  Theorem gform7_eq_gform8 : gform7 = gform8.
  Proof.
    unfold gform7, gform8.
    apply functional_extensionality; intro xs.
    unfold compose, semiring_sum.
    set (horner_op := fun x y => add_op (mul_op x y) mul_one).
    set (pair_step := fun x (uv : A * A) =>
      let (u, v) := uv in
      let w := horner_op x v in
      (add_op w u, w)).
    (* Apply the fold-scan fusion law *)
    rewrite <- (fold_scan_fusion add_op horner_op add_zero mul_one xs).
    reflexivity.
  Qed.

  (*
  =================================================================================
  MAIN CORRECTNESS RESULT FOR GENERAL SEMIRINGS
  =================================================================================

  All forms gform1 through gform8 work for ANY semiring!

  The fold-scan fusion law (gform7 → gform8) requires NO additional assumptions.
  It follows purely from the structure of fold and scan operations.
  *)

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

End KadaneTheorems.

(*
=================================================================================
KEY RESULTS SUMMARY
=================================================================================

THEOREM: Kadane's algorithm (gform8) is correct for ANY semiring.

Proof structure:
- gform1 (specification): sum of products over all subarrays
- gform2-gform4: List manipulation and fold promotion
- gform5-gform6: Horner's rule (generalised_horners_rule_right)
- gform6-gform7: Scan-fold relationship
- gform7-gform8: Fold-scan fusion (NO assumptions required!)

The entire derivation uses ONLY:
1. General semiring axioms (associativity, identities, distributivity)
2. List manipulation laws
3. The fold-scan fusion law (proven with zero assumptions)

This means Kadane's algorithm works for:
- Tropical semiring (max-plus): Maximum subarray problem
- Integer semiring: Sum of products
- Boolean semiring: Existence problems
- Any other semiring structure

See MaxSubarrayKadane.v for the specific tropical semiring instantiation.
*)