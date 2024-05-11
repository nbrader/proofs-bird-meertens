Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.

Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidMax.

(*
To Do:
  Swap out all instances of foldl with foldr because I think it'll be generally easier to work with.
  This is because:
    - I think proofs will turn out simpler because the recursive part looks the same as the hypothesis when performing induction.
    - Coq and Haskell agree on the order of the arguments of their right folder whereas they disagree for their left fold.
*)

(* Forms of MaxSegSum *)
Definition form1 : list (option R) -> option R := maximum ∘ map RsumWithNegInf ∘ segs.
Definition form2 : list (option R) -> option R := maximum ∘ map RsumWithNegInf ∘ concat ∘ map tails ∘ inits.
Definition form3 : list (option R) -> option R := maximum ∘ concat ∘ map (map RsumWithNegInf) ∘ map tails ∘ inits.
Definition form4 : list (option R) -> option R := maximum ∘ map maximum ∘ map (map RsumWithNegInf) ∘ map tails ∘ inits.
Definition form5 : list (option R) -> option R := maximum ∘ map (maximum ∘ map RsumWithNegInf ∘ tails) ∘ inits.
Definition form6 : list (option R) -> option R := maximum ∘ map (foldl RnonzeroSumWithNegInf None) ∘ inits.
Definition form7 : list (option R) -> option R := maximum ∘ scanl RnonzeroSumWithNegInf None.
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
  rewrite (compose_assoc _ _ _ _ (concat ∘ map tails) (map RsumWithNegInf) maximum).
  rewrite <- (compose_assoc _ _ _ _ (map tails) concat (map RsumWithNegInf)).
  rewrite (map_promotion RsumWithNegInf).
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
  rewrite (map_distr (map RsumWithNegInf) tails).
  rewrite (map_distr maximum (compose (map RsumWithNegInf) tails)).
  reflexivity.
Qed.

Theorem form4_eq_form6 : form5 = form6.
Proof.
  unfold form5.
  unfold form6.
  f_equal.
  f_equal.
  f_equal.
  apply horners_rule.
Qed.
