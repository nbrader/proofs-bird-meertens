(* Proof Strategy and Helper Lemmas for Bird-Meertens Formalization *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import BirdMeertens.Lemmas.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.
(* 
(* ==== LIBRARY EXPLORATION ==== *)

(* Let's check what theorems are available about Z.max and addition *)
Check Z.add_max_distr_l.  (* (x + max y z) = max (x + y) (x + z) *)
Check Z.add_max_distr_r.  (* (max y z + x) = max (y + x) (z + x) *)
Check Z.max_assoc.        (* max (max x y) z = max x (max y z) *)
Check Z.max_comm.         (* max x y = max y x *)
Check Z.max_idempotent.   (* max x x = x *)
Check Z.le_max_l.         (* x <= max x y *)
Check Z.le_max_r.         (* y <= max x y *)
Check Z.max_lub.          (* x <= z -> y <= z -> max x y <= z *)
Check Z.max_lub_lt.       (* x < z -> y < z -> max x y < z *)

(* Boolean ordering theorems *)
Check Z.leb_le.           (* Z.leb x y = true <-> x <= y *)
Check Z.leb_gt.           (* Z.leb x y = false <-> y < x *)
*)

(* ==== PROOF STRATEGY FOR nonNegPlus_distributes_over_max ==== *)

(*
Goal: distributes_over_max nonNegPlus
Meaning: forall s t x, nonNegPlus (Z.max s t) x = Z.max (nonNegPlus s x) (nonNegPlus t x)

Key insight: nonNegPlus a b = if Z.leb 0 (a + b) then a + b else 0

Strategy:
1. Use Z.add_max_distr_r to show: Z.max s t + x = Z.max (s + x) (t + x)
2. Case analysis on Z.leb conditions
3. Show that the boolean conditions are consistent with max properties

Missing lemmas needed:
- max_distributes_over_conditional: relationship between max and if-then-else
- consistency between Z.leb on sums and Z.leb on individual terms
*)

(* ==== CRITICAL HELPER LEMMAS ==== *)

(* The key distributivity property we need *)
Lemma max_add_distributes : forall s t x,
  Z.max s t + x = Z.max (s + x) (t + x).
Proof.
  intros. 
  rewrite Z.add_max_distr_r.
  reflexivity.
Qed.

(* Boolean consistency lemma - simpler version *)
Lemma leb_max_simple : forall s t x,
  Z.leb 0 (Z.max (s + x) (t + x)) = true -> 
  Z.leb 0 (s + x) = true \/ Z.leb 0 (t + x) = true.
Proof.
  intros s t x H.
  (* Convert boolean to proposition *)
  rewrite Z.leb_le in H.
  (* Case analysis on whether s + x >= 0 *)
  destruct (Z_le_dec 0 (s + x)) as [Hs | Hs].
  - (* Case: s + x >= 0 *)
    left. 
    rewrite Z.leb_le.
    exact Hs.
  - (* Case: s + x < 0 *)
    right.
    rewrite Z.leb_le.
    (* Since max >= 0 and s+x < 0, we must have t+x >= 0 *)
    apply Z.nle_gt in Hs.
    destruct (Z_le_dec 0 (t + x)) as [Ht | Ht].
    + exact Ht.
    + apply Z.nle_gt in Ht.
      (* Both s+x < 0 and t+x < 0, but max >= 0 - contradiction *)
      exfalso.
      assert (Z.max (s + x) (t + x) < 0).
      { apply Z.max_lub_lt; assumption. }
      apply (Z.lt_irrefl 0).
      apply Z.le_lt_trans with (m := Z.max (s + x) (t + x)).
      * exact H.
      * exact H0.
Qed.

(* Key lemma for the distributivity proof *)
Lemma nonNegPlus_cases : forall s t x,
  nonNegPlus (Z.max s t) x = 
  if Z.leb 0 (s + x) then
    if Z.leb 0 (t + x) then Z.max (s + x) (t + x)
    else if Z.leb (s + x) (t + x) then t + x else s + x
  else if Z.leb 0 (t + x) then t + x else 0.
Proof.
  intros s t x.
  unfold nonNegPlus.
  rewrite max_add_distributes.
  (* This requires careful case analysis *)
Admitted. (* Sketch for now *)

(* Simplified approach: direct case analysis *)
Lemma nonNegPlus_max_direct : forall s t x,
  nonNegPlus (Z.max s t) x = Z.max (nonNegPlus s x) (nonNegPlus t x).
Proof.
  intros s t x.
  unfold nonNegPlus.
  rewrite max_add_distributes.
  (* Case analysis on whether each sum is non-negative *)
  destruct (Z.leb 0 (s + x)) eqn:Hs, (Z.leb 0 (t + x)) eqn:Ht.
  
  (* Case 1: both s+x >= 0 and t+x >= 0 *)
  - (* Then max(s+x, t+x) >= 0, so nonNegPlus of max is the max itself *)
    (* And max(s+x, 0) = s+x and max(t+x, 0) = t+x *)
    simpl.
    assert (H_max_nonneg: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_le in Hs. apply Z.le_trans with (m := s + x).
      exact Hs. apply Z.le_max_l. }
    rewrite H_max_nonneg.
    reflexivity.
  
  (* Case 2: s+x >= 0 but t+x < 0 *)  
  - simpl.
    (* max(s+x, t+x) = s+x since s+x >= 0 > t+x *)
    assert (H_max_pos: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_le in Hs. rewrite Z.leb_gt in Ht.
      apply Z.le_trans with (m := s + x). exact Hs.
      apply Z.le_max_l. }
    rewrite H_max_pos.
    (* Now goal is: Z.max (s + x) (t + x) = (s + x) <|> 0 *)
    (* Since s+x >= 0 and t+x < 0, we have Z.max (s+x) (t+x) = s+x *)
    (* And s+x <|> 0 = Z.max (s+x) 0 = s+x since s+x >= 0 *)
    rewrite Z.leb_le in Hs. rewrite Z.leb_gt in Ht.
    assert (H_sx_ge_tx: s + x >= t + x). { lia. }
    rewrite Z.max_l.
    + rewrite Z.max_l; [reflexivity | exact Hs].
    + apply Z.ge_le. exact H_sx_ge_tx.
  
  (* Case 3: s+x < 0 but t+x >= 0 *)
  - simpl.
    assert (H_max_pos: Z.leb 0 (Z.max (s + x) (t + x)) = true).
    { apply Z.leb_le. rewrite Z.leb_gt in Hs. rewrite Z.leb_le in Ht.
      apply Z.le_trans with (m := t + x). exact Ht.
      apply Z.le_max_r. }
    rewrite H_max_pos.
    (* Now goal is: Z.max (s + x) (t + x) = 0 <|> (t + x) *)
    (* Since s+x < 0 and t+x >= 0, we have Z.max (s+x) (t+x) = t+x *)
    (* And 0 <|> t+x = Z.max 0 (t+x) = t+x since t+x >= 0 *)
    rewrite Z.leb_gt in Hs. rewrite Z.leb_le in Ht.
    assert (H_tx_ge_sx: t + x >= s + x). { lia. }
    rewrite Z.max_r.
    + rewrite Z.max_r; [reflexivity | exact Ht].
    + apply Z.ge_le. exact H_tx_ge_sx.
  
  (* Case 4: both s+x < 0 and t+x < 0 *)
  - (* Then max(s+x, t+x) < 0, so result is 0 *)
    (* And max(0, 0) = 0 *)
    simpl.
    assert (H_max_neg: Z.leb 0 (Z.max (s + x) (t + x)) = false).
    { apply Z.leb_gt. rewrite Z.leb_gt in Hs. rewrite Z.leb_gt in Ht.
      apply Z.max_lub_lt; assumption. }
    rewrite H_max_neg.
    reflexivity.
Qed.

(* ==== PROOF STRATEGY FOR generalised_horners_rule ==== *)

(*
Goal: fold_right Z.max 0 ∘ map (fold_right nonNegPlus 0) ∘ inits = 
      fold_right (fun x y => nonNegPlus x y <|> 0) 0

Base case: [] -> fold_right Z.max 0 (map ... (inits [])) = fold_right ... 0 []
  - inits [] = [[]]
  - map (fold_right nonNegPlus 0) [[]] = [0]  
  - fold_right Z.max 0 [0] = Z.max 0 0 = 0
  - fold_right ... 0 [] = 0
  ✓ Complete

Inductive case: x :: xs
  Left side: fold_right Z.max 0 (map (fold_right nonNegPlus 0) (inits (x :: xs)))
  - inits (x :: xs) = [] :: map (cons x) (inits xs)
  - map (fold_right nonNegPlus 0) ([] :: map (cons x) (inits xs))
    = 0 :: map (fold_right nonNegPlus 0) (map (cons x) (inits xs))
  - fold_right Z.max 0 (0 :: ...) = Z.max 0 (fold_right Z.max 0 (...))

  Right side: fold_right (fun x0 y => nonNegPlus x0 y <|> 0) 0 (x :: xs)
  = nonNegPlus x (fold_right ... 0 xs) <|> 0

Key insight: Need to show that 
  fold_right Z.max 0 (map (fold_right nonNegPlus 0) (map (cons x) (inits xs)))
  equals something related to x and the result from xs.

Missing lemmas needed:
- Properties of map (cons x) on inits
- Relationship between fold_right nonNegPlus on prefixes and the Horner-like operation
- Connection between nonNegPlus and the max-or-zero operation
*)

(* Helper lemma: nonNegPlus with 0 gives max-like behavior *)
Lemma nonNegPlus_max_zero : forall x y,
  nonNegPlus x y <|> 0 = Z.max (if Z.leb 0 (x + y) then x + y else 0) 0.
Proof.
  intros x y.
  unfold nonNegPlus.
  destruct (Z.leb 0 (x + y)) eqn:H.
  - simpl. rewrite Z.max_l; [reflexivity | rewrite Z.leb_le in H; assumption].
  - simpl. rewrite Z.max_r; [reflexivity | reflexivity].
Qed.

(* ==== PROOF STRATEGY FOR form5_eq_form6 ==== *)

(*
Goal: form5 = form6
Where:
- form5 = nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails  
- form6 = nonNegMaximum ∘ map (fold_right nonNegPlus 0) ∘ tails

Strategy:
1. Apply functional extensionality
2. For any list xs, need to show:
   (nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits)) (tails xs) =
   (nonNegMaximum ∘ map (fold_right nonNegPlus 0)) (tails xs)
3. This reduces to showing: nonNegMaximum ∘ map nonNegSum ∘ inits = fold_right nonNegPlus 0
4. This is exactly generalised_horners_rule!

Dependencies: Needs generalised_horners_rule to be complete first.
*)

(* ==== IMPLEMENTATION PLAN ==== *)

(*
Phase 1: Basic helper lemmas (simple)
- nonNegPlus properties with 0
- Basic max properties we need
- Boolean condition lemmas

Phase 2: Intermediate lemmas (moderate)  
- Distributivity components
- List operation properties
- Relationship between different fold operations

Phase 3: Main theorems (complex)
- Complete generalised_horners_rule using Phase 1&2 lemmas
- Complete nonNegPlus_distributes_over_max using distributivity
- Complete form5_eq_form6 using generalised_horners_rule

Priority order:
1. nonNegPlus_distributes_over_max (has clearer path forward)
2. generalised_horners_rule (more complex but well-structured)  
3. form5_eq_form6 (depends on #2)
*)