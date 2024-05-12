Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidRLBmax.
Require Import BirdMeertens.MonoidRLBplus.
Require Import BirdMeertens.RealsWithLowerBound.

(* Forms of MaxSegSum *)
Definition form1 : list RLB -> RLB := RLBmaximum ∘ map RLBsum ∘ segs.
Definition form2 : list RLB -> RLB := RLBmaximum ∘ map RLBsum ∘ concat ∘ map inits ∘ tails.
Definition form3 : list RLB -> RLB := RLBmaximum ∘ concat ∘ map (map RLBsum) ∘ map inits ∘ tails.
Definition form4 : list RLB -> RLB := RLBmaximum ∘ map RLBmaximum ∘ map (map RLBsum) ∘ map inits ∘ tails.
Definition form5 : list RLB -> RLB := RLBmaximum ∘ map (RLBmaximum ∘ map RLBsum ∘ inits) ∘ tails.
Definition form6 : list RLB -> RLB := RLBmaximum ∘ map (fold_right RLBplus (Some 0)) ∘ tails.
Definition form7 : list RLB -> RLB := RLBmaximum ∘ scan_right RLBplus (Some 0).
Definition form8 : list RLB -> RLB := fst ∘ fold_right RLBmaxSoFarAndPreviousSum (Some 0,Some 0).

Theorem form1_eq_form2 : form1 = form2.
Proof.
  reflexivity.
Qed.

Theorem form2_eq_form3 : form2 = form3.
Proof.
  unfold form2.
  unfold form3.
  f_equal.
  rewrite compose_assoc.
  rewrite (compose_assoc _ _ _ _ (concat ∘ map inits) (map RLBsum) RLBmaximum).
  rewrite <- (compose_assoc _ _ _ _ (map inits) concat (map RLBsum)).
  rewrite (map_promotion RLBsum).
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
  rewrite (map_distr (map RLBsum) inits).
  rewrite (map_distr RLBmaximum (compose (map RLBsum) inits)).
  reflexivity.
Qed.

Theorem form4_eq_form6 : form5 = form6.
Proof.
  unfold form5.
  unfold form6.
  f_equal.
  f_equal.
  f_equal.
  (* apply horners_rule. *)
Admitted.
