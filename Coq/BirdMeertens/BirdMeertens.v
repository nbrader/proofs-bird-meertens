Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidMax.

(* Forms of MaxSegSum *)
Definition form1 : list (option R) -> option R := maximum ∘ map Rsum ∘ segs.
Definition form2 : list (option R) -> option R := maximum ∘ map Rsum ∘ concat ∘ map tails ∘ inits.
Definition form3 : list (option R) -> option R := maximum ∘ concat ∘ map (map Rsum) ∘ map tails ∘ inits.
Definition form4 : list (option R) -> option R := maximum ∘ map maximum ∘ map (map Rsum) ∘ map tails ∘ inits.
Definition form5 : list (option R) -> option R := maximum ∘ map (maximum ∘ map Rsum ∘ tails) ∘ inits.
Definition form6 : list (option R) -> option R := maximum ∘ map (foldl RnonzeroSum None) ∘ inits.
Definition form7 : list (option R) -> option R := maximum ∘ scanl RnonzeroSum None.
Definition form8 : list (option R) -> option R := fst ∘ foldl RmaxWithNegInfSoFarAndPreviousNonzeroSum (None,None).

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
  rewrite (compose_assoc _ _ _ _ (concat ∘ map tails) (map Rsum) maximum).
  rewrite <- (compose_assoc _ _ _ _ (map tails) concat (map Rsum)).
  rewrite (map_promotion Rsum).
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
  rewrite (map_distr (map Rsum) tails).
  rewrite (map_distr maximum (compose (map Rsum) tails)).
  reflexivity.
Qed.
