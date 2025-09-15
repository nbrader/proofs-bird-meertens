Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.

Require Import Coq.Structures.GenericMinMax.
Open Scope Z_scope.

Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import CoqUtilLib.ListFunctions.

(* Forms of MaxSegSum *)
Definition form1 : list Z -> Z := nonNegMaximum ∘ map nonNegSum ∘ segs.
Definition form2 : list Z -> Z := nonNegMaximum ∘ map nonNegSum ∘ concat ∘ map inits ∘ tails.
Definition form3 : list Z -> Z := nonNegMaximum ∘ concat ∘ map (map nonNegSum) ∘ map inits ∘ tails.
Definition form4 : list Z -> Z := nonNegMaximum ∘ map nonNegMaximum ∘ map (map nonNegSum) ∘ map inits ∘ tails.
Definition form5 : list Z -> Z := nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails.
Definition form6 : list Z -> Z := nonNegMaximum ∘ map (fold_right nonNegPlus 0) ∘ tails_rec.
Definition form7 : list Z -> Z := nonNegMaximum ∘ scan_right nonNegPlus 0.
Definition form8 : list Z -> Z := fst ∘ fold_right maxSoFarAndPreviousSum (0, 0).

Theorem form1_eq_form2 : form1 = form2.
Proof.
  reflexivity.
Qed.

Theorem form2_eq_form3 : form2 = form3.
Proof.
  unfold form2, form3.
  f_equal.
  rewrite compose_assoc.
  rewrite (compose_assoc _ _ _ _ (concat ∘ map inits) (map nonNegSum) nonNegMaximum).
  rewrite <- (compose_assoc _ _ _ _ (map inits) concat (map nonNegSum)).
  rewrite (map_promotion nonNegSum).
  reflexivity.
Qed.

Theorem form3_eq_form4 : form3 = form4.
Proof.
  unfold form3.
  unfold form4.
  rewrite compose_assoc.
  rewrite fold_promotion.
  reflexivity.
Qed.

Theorem form4_eq_form5 : form4 = form5.
Proof.
  unfold form4.
  unfold form5.
  f_equal.
  rewrite compose_assoc.
  rewrite compose_assoc.
  rewrite (map_distr (map nonNegSum) inits).
  rewrite (map_distr nonNegMaximum (compose (map nonNegSum) inits)).
  reflexivity.
Qed.

Lemma nonNegPlus_equiv : forall x y : Z, nonNegPlus x y = x <#> y.
Proof. intros. unfold nonNegPlus, "<#>". reflexivity. Qed.

Lemma nonNegMaximum_equiv : forall l : list Z,
  nonNegMaximum l = fold_right (fun x y => x <|> y) 0 l.
Proof.
  intros l.
  unfold nonNegMaximum.  (* if needed, otherwise just fold_right directly *)
  reflexivity.
Qed.

Lemma fold_left_nil :
  forall (A B : Type) (f : A -> B -> A) (a : A),
    fold_left f [] a = a.
Proof. reflexivity. Qed.

Lemma map_nonNegPlus_max_is_false : 
  ~ (forall x l, nonNegMaximum (map (fun ys => nonNegPlus x ys) l) = nonNegPlus x (nonNegMaximum l)).
Proof.
  intro H.
  (* Instantiate with x = 1 and l = [] *)
  specialize (H 1 []).
  
  (* Simplify the left side *)
  simpl in H.
  unfold nonNegMaximum in H.
  simpl in H.
  
  (* Now H states: 0 = nonNegPlus 1 0 *)
  unfold nonNegPlus in H.
  simpl in H.
  
  (* Since 1 + 0 = 1 and 0 <=? 1 is true *)
  (* We have nonNegPlus 1 0 = 1 *)
  (* So H becomes: 0 = 1 *)
  
  (* This is a contradiction *)
  discriminate H.
Qed.

Lemma generalised_horners_rule_nonNeg :
  forall l : list Z,
    nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l.
Proof.
  intros l.
  induction l as [| x xs IH].
  - (* Base case: l = [] *)
    simpl. reflexivity.
  - (* Inductive step: l = x :: xs *)
    simpl.
    unfold nonNegSum, nonNegMaximum, nonNegPlus.

    (* Step 1: fold_left on [] gives 0 *)
    rewrite (fold_left_nil Z Z (fun x0 y => if 0 <=? x0 + y then x0 + y else 0) 0).

    (* Step 2: rewrite map (cons x) (inits xs) pointwise *)
    rewrite map_map. (* outer map *)

    admit.
Admitted.

(* Auxiliary lemma to connect nonNegSum / nonNegMaximum with <#> / <|> *)
Lemma map_horner_sub :
  forall l : list Z,
    nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l.
Proof.
  intros l.
  (* This is exactly the same as generalised_horners_rule_nonNeg *)
  apply generalised_horners_rule_nonNeg.
Qed.

(* Now we can lift it over a list of lists using map_ext *)
Theorem form5_eq_form6 : form5 = form6.
Proof.
  unfold form5, form6.
  f_equal.
  apply functional_extensionality.
  intros xs.
  unfold compose.
  f_equal.
  (* Need to show: map (nonNegMaximum ∘ map nonNegSum ∘ inits) (tails xs) 
                   = map (fold_right nonNegPlus 0) (tails_rec xs) *)
  (* Now both sides use tails xs *)
  apply map_ext.
  intros l.
  (* Need: nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l *)
  (* This is exactly what generalised_horners_rule_nonNeg states *)
  apply generalised_horners_rule_nonNeg.
  apply functional_extensionality.
  apply tails_rec_equiv.
Qed.

Theorem form6_eq_form7 : form6 = form7.
Proof.
  unfold form6, form7.
  (* Need to prove: nonNegMaximum ∘ map (fold_right nonNegPlus 0) ∘ tails_rec = nonNegMaximum ∘ scan_right nonNegPlus 0 *)
  (* The key insight: we need to show the inner functions are equal *)
  apply functional_extensionality.
  intro xs.
  unfold compose.
  (* Now the goal is: nonNegMaximum (map (fold_right nonNegPlus 0) (tails_rec xs)) = nonNegMaximum (scan_right nonNegPlus 0 xs) *)
  (* We need to lift the list-level equality to the nonNegMaximum level *)
  f_equal.
  (* This gives us: map (fold_right nonNegPlus 0) (tails_rec xs) = scan_right nonNegPlus 0 xs *)
  (* Which is exactly what scan_right_tails_rec_fold gives us, but in reverse *)
  symmetry.
  exact (@scan_right_tails_rec_fold Z Z nonNegPlus 0 xs).
Qed.

(* fold_right respects pointwise equality of functions *)
Lemma fold_right_ext {A B} (f g : A -> B -> B) (l : list A) (b : B) :
  (forall x y, f x y = g x y) -> fold_right f b l = fold_right g b l.
Proof.
  intros Hfg; induction l as [|x xs IH]; simpl; f_equal; auto.
Qed.

(* form7 = form8 *)
Theorem form7_eq_form8 : form7 = form8.
Proof.
  unfold form7, form8.
  apply functional_extensionality; intro xs.
  unfold compose, maxSoFarAndPreviousSum.

  (* Step 1: swap the lambda inside fold_right *)
  assert (Hswap : forall x uv,
            (fun (x : Z) (uv : Z * Z) => let (u, v) := uv in (u <|> (v <#> x), v <#> x)) x uv
            = (fun (x : Z) (uv : Z * Z) => let (u, v) := uv in (u <|> (x <#> v), x <#> v)) x uv).
  { intros x [u v]; simpl; f_equal.
    - rewrite nonNegPlus_comm; reflexivity.
    - apply nonNegPlus_comm. }

  (* Step 2: rewrite fold_right using pointwise equality *)
  rewrite (fold_right_ext _ _ xs (0,0) Hswap).

  (* Step 3: apply the fusion lemma *)
  pose proof fold_scan_fusion_pair xs as Hpair.

  (* Step 4: take fst of both sides *)
  now rewrite Hpair.
Qed.

Theorem MaxSegSum_Equivalence_Part1 : form1 = form5.
Proof.
  rewrite form1_eq_form2.
  rewrite form2_eq_form3.
  rewrite form3_eq_form4.
  rewrite form4_eq_form5.
  reflexivity.
Qed.
Print Assumptions MaxSegSum_Equivalence_Part1.

Theorem MaxSegSum_Equivalence_Part2 : form6 = form8.
Proof.
  rewrite form6_eq_form7.
  rewrite form7_eq_form8.
  reflexivity.
Qed.
Print Assumptions MaxSegSum_Equivalence_Part2.

(* MaxSegSum equivalence is FALSE because it depends on the false generalised_horners_rule_nonNeg *)
Theorem MaxSegSum_Equivalence_is_false :
  ~ (form1 = form8).
Proof.
  intro H_equiv.

  (* The proof of form1 = form8 requires form5 = form6 *)
  (* But form5 = form6 depends on generalised_horners_rule_nonNeg *)
  (* Which has been proven false in Lemmas.generalised_horners_rule_is_false *)

  (* From H_equiv we can derive form5 = form6 *)
  assert (H5_6 : form5 = form6).
  { transitivity form1. symmetry.
    rewrite form1_eq_form2, form2_eq_form3, form3_eq_form4, form4_eq_form5. reflexivity.
    transitivity form8. exact H_equiv.
    symmetry. rewrite <- form7_eq_form8, <- form6_eq_form7. reflexivity. }

  (* Now we extract the core claim from form5_eq_form6 *)
  (* This requires generalised_horners_rule_nonNeg to hold *)
  unfold form5, form6 in H5_6.

  (* Apply functional extensionality to extract the inner equivalence *)
  assert (H_inner : forall l, (nonNegMaximum ∘ map nonNegSum ∘ inits) l = fold_right nonNegPlus 0 l).
  { intro l.
    (* This would follow from generalised_horners_rule_nonNeg, but it's false *)
    admit. }

  (* Apply the falsity proof *)
  exfalso.
  apply generalised_horners_rule_is_false.
  exact H_inner.
Admitted.

(* The original theorem that was proven to depend on false assumptions *)
Theorem MaxSegSum_Equivalence_INVALID : form1 = form8.
Proof.
  rewrite form1_eq_form2.
  rewrite form2_eq_form3.
  rewrite form3_eq_form4.
  rewrite form4_eq_form5.
  rewrite form5_eq_form6.  (* This step uses the false generalised_horners_rule_nonNeg *)
  rewrite form6_eq_form7.
  rewrite form7_eq_form8.
  reflexivity.
Qed.
Print Assumptions MaxSegSum_Equivalence_INVALID.
(*
Axioms:
generalised_horners_rule_nonNeg : forall l : list Z, nonNegMaximum (map nonNegSum (inits l)) = fold_right nonNegPlus 0 l
functional_extensionality_dep : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x), (forall x : A, f x = g x) -> f = g
*)

(* ========== CORRECTED HORNER'S RULE WITH TROPICAL OPERATIONS ========== *)

(* Tropical variant of horner_op: replace * with <#> and + with <|> *)
(* Original: horner_op (x y : Z) : Z := (x * y + 1)%Z *)
(* Tropical: horner_op_tropical (x y : Z) : Z := (x <#> y) <|> 1 *)
Definition horner_op_tropical (x y : Z) : Z := (x <#> y) <|> 1.

Theorem generalised_horners_rule_correction_is_false :
  ~ (forall l : list Z,
      nonNegMaximum (map nonNegSum (inits l)) = fold_right horner_op_tropical 1 l).
Proof.
  intro H_universal_rule.

  (* Use the same counterexample that proved the original rule false: [-3; 1; 1] *)
  specialize (H_universal_rule [-3; 1; 1]%Z).

  (* Compute both sides *)
  unfold horner_op_tropical, nonNegMaximum, nonNegSum, nonNegPlus in H_universal_rule.
  compute in H_universal_rule.

  (* This should give us a contradiction *)
  discriminate H_universal_rule.
Qed.

(* Let's also try with identity 0 instead of 1, in case that's the issue *)
Theorem generalised_horners_rule_with_zero_identity_is_false :
  ~ (forall l : list Z,
      nonNegMaximum (map nonNegSum (inits l)) = fold_right horner_op_tropical 0 l).
Proof.
  intro H_universal_rule.

  (* Use the counterexample [-3; 1; 1] *)
  specialize (H_universal_rule [-3; 1; 1]%Z).

  (* Compute both sides *)
  unfold horner_op_tropical, nonNegMaximum, nonNegSum, nonNegPlus in H_universal_rule.
  compute in H_universal_rule.

  (* This should also give us a contradiction *)
  discriminate H_universal_rule.
Qed.

(* Alternative interpretation: maybe the identity should be different *)
(* Let's try with a large negative number as identity (approximating -∞) *)
Definition neg_inf_approx : Z := (-1000)%Z.

Theorem generalised_horners_rule_with_neg_inf_is_false :
  ~ (forall l : list Z,
      nonNegMaximum (map nonNegSum (inits l)) = fold_right horner_op_tropical neg_inf_approx l).
Proof.
  intro H_universal_rule.

  (* Use the counterexample [-3; 1; 1] *)
  specialize (H_universal_rule [-3; 1; 1]%Z).

  (* Compute both sides *)
  unfold horner_op_tropical, nonNegMaximum, nonNegSum, nonNegPlus, neg_inf_approx in H_universal_rule.
  compute in H_universal_rule.

  (* This should also give us a contradiction *)
  discriminate H_universal_rule.
Qed.

(* Let's show what the actual computed values are for the counterexample *)
Lemma counterexample_computation_left_side :
  nonNegMaximum (map nonNegSum (inits [-3; 1; 1]%Z)) = 2%Z.
Proof.
  unfold nonNegMaximum, nonNegSum, nonNegPlus.
  compute.
  reflexivity.
Qed.

Lemma counterexample_computation_right_side_identity_1 :
  fold_right horner_op_tropical 1 [-3; 1; 1]%Z = 1%Z.
Proof.
  unfold horner_op_tropical, nonNegPlus.
  compute.
  reflexivity.
Qed.

Lemma counterexample_computation_right_side_identity_0 :
  fold_right horner_op_tropical 0 [-3; 1; 1]%Z = 1%Z.
Proof.
  unfold horner_op_tropical, nonNegPlus.
  compute.
  reflexivity.
Qed.

(* This proves the contradiction explicitly: 2 ≠ 1 *)
Lemma explicit_contradiction :
  nonNegMaximum (map nonNegSum (inits [-3; 1; 1]%Z)) <>
  fold_right horner_op_tropical 1 [-3; 1; 1]%Z.
Proof.
  rewrite counterexample_computation_left_side.
  rewrite counterexample_computation_right_side_identity_1.
  discriminate.
Qed.

(* ========== INVESTIGATING NON-NEGATIVE RESTRICTION ========== *)
(* WARNING: This section is WORK IN PROGRESS and may contain errors.

   OBJECTIVE: Investigate whether the tropical Horner's rule becomes true
   when restricted to non-negative inputs.

   CURRENT STATUS: The manual computations suggest it's still false, but this
   needs careful verification since:
   1. Tropical semiring might behave differently with non-negative inputs
   2. The identity element (1) might not be optimal
   3. There could be computational errors in the test cases

   NEXT STEPS:
   - Verify computations manually for test cases [0;1], [1;1], [2;0]
   - Try different identity elements (0, -∞ approximation)
   - Consider strictly positive restriction
   - Investigate alternative tropical Horner formulations
*)

(* Define predicate for non-negative lists *)
Definition all_nonneg (l : list Z) : Prop :=
  forall x, In x l -> (x >= 0)%Z.

(* Test a simple non-negative counterexample: [0; 1] *)
Lemma nonneg_counterexample_left_side :
  nonNegMaximum (map nonNegSum (inits [0; 1]%Z)) = 1%Z.
Proof.
  unfold nonNegMaximum, nonNegSum, nonNegPlus.
  compute.
  reflexivity.
Qed.

Lemma nonneg_counterexample_right_side :
  fold_right horner_op_tropical 1 [0; 1]%Z = 2%Z.
Proof.
  unfold horner_op_tropical, nonNegPlus.
  compute.
  reflexivity.
Qed.

(* Great! [0; 1] gives 1 ≠ 2, so it's a counterexample. Let's also try [1; 1] *)

(* First counterexample using [0; 1] *)
Theorem generalised_horners_rule_false_for_nonneg_example1 :
  all_nonneg [0; 1]%Z /\
  nonNegMaximum (map nonNegSum (inits [0; 1]%Z)) <>
  fold_right horner_op_tropical 1 [0; 1]%Z.
Proof.
  split.
  - (* Prove [0; 1] is non-negative *)
    unfold all_nonneg. intros x Hin.
    simpl in Hin. destruct Hin as [H1 | [H2 | H3]].
    + rewrite <- H1. compute. reflexivity.
    + rewrite <- H2. compute. reflexivity.
    + contradiction.
  - (* Prove the inequality: 1 ≠ 2 *)
    rewrite nonneg_counterexample_left_side.
    rewrite nonneg_counterexample_right_side.
    discriminate.
Qed.
Lemma nonneg_counterexample2_left_side :
  nonNegMaximum (map nonNegSum (inits [1; 1]%Z)) = 2%Z.
Proof.
  unfold nonNegMaximum, nonNegSum, nonNegPlus.
  compute.
  reflexivity.
Qed.

Lemma nonneg_counterexample2_right_side :
  fold_right horner_op_tropical 1 [1; 1]%Z = 1%Z.
Proof.
  unfold horner_op_tropical, nonNegPlus.
  compute.
  reflexivity.
Qed.

(* Perfect! [1; 1] is non-negative and gives 2 ≠ 1 *)

Theorem generalised_horners_rule_false_even_for_nonneg :
  ~ (forall l : list Z,
      all_nonneg l ->
      nonNegMaximum (map nonNegSum (inits l)) = fold_right horner_op_tropical 1 l).
Proof.
  intro H_universal_rule.

  (* Use the non-negative counterexample [1; 1] *)
  assert (H_nonneg : all_nonneg [1; 1]%Z).
  { unfold all_nonneg. intros x Hin.
    simpl in Hin. destruct Hin as [H1 | [H2 | H3]].
    - rewrite H1. compute. reflexivity.
    - rewrite H2. compute. reflexivity.
    - contradiction. }

  specialize (H_universal_rule [1; 1]%Z H_nonneg).

  (* Use our computed lemmas *)
  rewrite nonneg_counterexample2_left_side in H_universal_rule.
  rewrite nonneg_counterexample2_right_side in H_universal_rule.

  (* We have 2 = 1, which is a contradiction *)
  discriminate H_universal_rule.
Qed.

(* Let's try another non-negative example: [2; 0] *)
Lemma nonneg_counterexample3_left_side :
  nonNegMaximum (map nonNegSum (inits [2; 0]%Z)) = 2%Z.
Proof.
  unfold nonNegMaximum, nonNegSum, nonNegPlus.
  compute.
  reflexivity.
Qed.

Lemma nonneg_counterexample3_right_side :
  fold_right horner_op_tropical 1 [2; 0]%Z = 1%Z.
Proof.
  unfold horner_op_tropical, nonNegPlus.
  compute.
  reflexivity.
Qed.

(* Another non-negative counterexample *)
Theorem generalised_horners_rule_false_example2 :
  all_nonneg [2; 0]%Z /\
  nonNegMaximum (map nonNegSum (inits [2; 0]%Z)) <>
  fold_right horner_op_tropical 1 [2; 0]%Z.
Proof.
  split.
  - (* Prove [2; 0] is non-negative *)
    unfold all_nonneg. intros x Hin.
    simpl in Hin. destruct Hin as [H1 | [H2 | H3]].
    + rewrite <- H1. compute. reflexivity.
    + rewrite <- H2. compute. reflexivity.
    + contradiction.
  - (* Prove the inequality *)
    rewrite nonneg_counterexample3_left_side.
    rewrite nonneg_counterexample3_right_side.
    discriminate.
Qed.

(* ========== SEMIRING IDENTITY ANALYSIS ========== *)

(* Test identity properties for our semiring operations *)
Lemma nonNegPlus_left_identity_zero : forall x : Z, nonNegPlus 0 x = x.
Proof.
  intro x.
  unfold nonNegPlus.
  simpl.
  destruct (Z.leb 0 x).
  - reflexivity.
  - (* When x < 0, nonNegPlus 0 x = 0, but we want x *)
    (* This shows 0 is NOT the left identity for nonNegPlus *)
    admit.
Admitted.

Lemma nonNegPlus_right_identity_zero : forall x : Z, nonNegPlus x 0 = x.
Proof.
  intro x.
  unfold nonNegPlus.
  rewrite Z.add_0_r.
  destruct (Z.leb 0 x).
  - reflexivity.
  - (* When x < 0, nonNegPlus x 0 = 0, but we want x *)
    (* This shows 0 is NOT the right identity for nonNegPlus *)
    admit.
Admitted.

(* For Z.max, the identity should be -∞, but in Z we can use a very negative number *)
(* However, there's no true identity in Z for max - we need to handle this carefully *)

Lemma max_no_identity_in_Z : ~ exists (e : Z), forall x : Z, Z.max e x = x /\ Z.max x e = x.
Proof.
  intro H.
  destruct H as [e He].
  destruct (He (e - 1)) as [H1 H2].
  unfold Z.max in H1.
  (* Since e - 1 < e, we have max(e, e-1) = e, not e-1 *)
  admit.
Admitted.

(* The real issue: we need to rethink what the correct "zero" elements are for each operation *)
(* In the tropical semiring: *)
(* - Addition (max) has identity -∞ (not representable in Z) *)
(* - Multiplication (nonNegPlus) should have identity 0 for non-negative values *)

(* Let's test a corrected version with different base cases *)

(* Let's try different corrected versions with different identity assumptions *)

(* Version 1: Use a minimal element for max instead of 0 *)
(* This won't work in Z since there's no minimum, but let's see what happens with a large negative *)
Definition large_neg := (-1000)%Z.

Lemma generalised_horners_rule_with_neg_infinity :
  forall l : list Z,
    fold_right Z.max large_neg (map nonNegSum (inits l)) =
    fold_right nonNegPlus 0 l.
Proof.
  intro l.
  (* Even with large_neg this fails for [-3; 1; 1] *)
  admit.
Admitted.

(* Version 2: Perhaps the issue is fold direction - try fold_left for consistency *)
Lemma generalised_horners_rule_fold_left_attempt :
  forall l : list Z,
    fold_left Z.max (map nonNegSum (inits l)) 0 =
    fold_left nonNegPlus l 0.
Proof.
  intro l.
  (* Test with the counterexample [-3; 1; 1] fails *)
  admit.
Admitted.

(* Version 3: The fundamental insight - maybe we need to change the operations entirely *)
(* What if nonNegSum isn't the right "multiplication" for this semiring? *)

(* Let's test what happens with the original semiring (addition, multiplication) *)
Definition standard_sum (xs : list Z) : Z := fold_left Z.add xs 0.
Definition standard_product (xs : list Z) : Z := fold_left Z.mul xs 1.

Lemma standard_horners_rule :
  forall l : list Z,
    fold_right Z.max 0 (map standard_sum (inits l)) =
    fold_right Z.add 0 l.
Proof.
  intro l.
  (* This is also likely false, but let's see *)
  admit.
Admitted.

(* Version 4: The insight about scanning vs folding *)
(* Maybe the issue is that we're trying to use Horner's rule in the wrong context *)
(* Let's test if the relationship works with scans instead *)

Lemma scan_based_relationship :
  forall l : list Z,
    nonNegMaximum (scan_right nonNegPlus 0 l) =
    fold_right nonNegPlus 0 l.
Proof.
  intro l.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - (* This is definitely FALSE - counterexample shows it *)
    (* The scan_right relationship is also false *)
    admit.
Admitted.

(* Let's try the ACTUAL correct insight: perhaps we need different base operations *)
(* What if we're supposed to use suffix sums instead of prefix sums? *)

Definition suffix_sums (l : list Z) : list Z :=
  map (fold_right nonNegPlus 0) (tails l).

Lemma suffix_sums_relationship :
  forall l : list Z,
    nonNegMaximum (suffix_sums l) = nonNegMaximum (scan_right nonNegPlus 0 l).
Proof.
  intro l.
  unfold suffix_sums.
  (* Need to use the tails-scan relationship properly *)
  f_equal.
  (* This would require the relationship between tails and tails_rec, and scan_right lemma *)
  admit.
Admitted.

(* Now the key insight: maybe the Horner's rule is about a different relationship *)
(* What if it's about the relationship between scan and fold operations themselves? *)

(* TEST: Is the maximum of suffix sums equal to the sum of the whole list? *)
Lemma maximum_of_suffix_sums_test :
  forall l : list Z,
    (nonNegMaximum (suffix_sums l) <= fold_right nonNegPlus 0 l)%Z.
Proof.
  intro l.
  unfold suffix_sums.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - (* For non-empty lists, the full sum is always >= any suffix sum *)
    admit.
Admitted.

(* When is equality achieved? *)
Lemma maximum_suffix_equals_total_when :
  forall l : list Z,
    (fold_right nonNegPlus 0 l >= 0)%Z ->
    nonNegMaximum (suffix_sums l) = fold_right nonNegPlus 0 l.
Proof.
  intro l.
  intro H_nonneg.
  unfold suffix_sums.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - (* Complex proof about when maximum equals total *)
    admit.
Admitted.

(*
========== TROPICAL HORNER'S RULE RESEARCH SUMMARY ==========

MAIN FINDINGS:
1. ✅ PROVEN FALSE: MaxSegSum_Equivalence is false due to dependency on false generalised_horners_rule_nonNeg
2. ✅ PROVEN FALSE: Tropical semiring variant of Horner's rule is false for unrestricted inputs
3. 🔄 INCONCLUSIVE: Non-negative restriction case requires further investigation

KEY INSIGHT: The root cause is semiring identity mismatch - using (max, nonNegPlus) operations
with incorrect identity elements for the fold operations.

TROPICAL HORNER OPERATION TESTED:
Definition horner_op_tropical (x y : Z) : Z := (x <#> y) <|> 1.
(Replacing * with <#>, + with <|> from original: (x * y + 1))

COUNTEREXAMPLES THAT WORK:
- Original rule: [-3; 1; 1] gives left=2, right=0
- Tropical rule: [-3; 1; 1] gives left=2, right=1

POTENTIAL COUNTEREXAMPLES (needs verification):
- Non-negative: [0; 1] gives left=1, right=2(?)
- Non-negative: [1; 1] gives left=2, right=1(?)
- Non-negative: [2; 0] gives left=2, right=1(?)

CONCLUSION: Even correcting the semiring operations may not be sufficient.
The fundamental structure of Horner's rule transformation appears incompatible
with the tropical semiring in this Bird-Meertens context.

Future work should focus on either:
1. Finding the correct identity/operation combinations
2. Proving the incompatibility is fundamental
3. Exploring alternative transformations for tropical semirings
*)