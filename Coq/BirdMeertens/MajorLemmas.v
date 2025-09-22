(* Major Lemmas - Immediate Dependencies of BirdMeertens.v *)
(* This file contains theorems that BirdMeertens.v depends on directly *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export BirdMeertens.Lemmas.
Require Export CoqUtilLib.ListFunctions.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

(* ===== IMMEDIATE DEPENDENCIES FROM BirdMeertens.v ===== *)
(* These lemmas are moved here from Lemmas.v to clearly separate *)
(* immediate dependencies (used directly by BirdMeertens.v) from *)
(* indirect dependencies (used by these lemmas) *)

(* map_promotion - used in form2_eq_form3 *)
Lemma map_promotion {A : Type} : forall (f : (list A) -> A),
  map f ∘ concat = concat ∘ map (map f).
Admitted. (* Moved from Lemmas.v *)

(* fold_promotion - used in form3_eq_form4 *)
Lemma fold_promotion : nonNegMaximum ∘ concat = nonNegMaximum ∘ map nonNegMaximum.
Admitted. (* Moved from Lemmas.v *)

(* nonNegPlus_comm - used in form7_eq_form8 *)
Lemma nonNegPlus_comm : forall x y : Z, nonNegPlus x y = nonNegPlus y x.
Admitted. (* Moved from Lemmas.v *)

(* fold_scan_fusion_pair - used in form7_eq_form8 *)
Lemma fold_scan_fusion_pair :
  forall (xs : list Z),
    fold_right
      (fun x uv => let '(u, v) := uv in (Z.max u (nonNegPlus x v), nonNegPlus x v))
      (0, 0) xs
    =
    (fold_right Z.max 0 (scan_right nonNegPlus 0 xs),
     fold_right nonNegPlus 0 xs).
Admitted. (* Moved from Lemmas.v *)

(* generalised_horners_rule - used in form5_eq_form6 *)
Lemma generalised_horners_rule : fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits.
Admitted. (* Moved from Lemmas.v *)

(* generalised_horners_rule' - used in form5_eq_form6 *)
Lemma generalised_horners_rule' : nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec = nonNegMaximum ∘ map nonNegSum ∘ tails_rec.
Admitted. (* Moved from Lemmas.v *)

(* fold_right_ext - used in form7_eq_form8 *)
Lemma fold_right_ext : forall {A B : Type} (f g : A -> B -> B) (xs : list A) (init : B),
  (forall x acc, f x acc = g x acc) ->
  fold_right f init xs = fold_right g init xs.
Admitted. (* Moved from Lemmas.v *)

(* ===== DUAL FORM DEPENDENCIES ===== *)

(* fold_promotion_dual - used in form3_dual_eq_form4_dual *)
Lemma fold_promotion_dual : nonNegMaximum_dual ∘ (concat (A:=Z)) = nonNegMaximum_dual ∘ map nonNegMaximum_dual.
Admitted. (* Moved from Lemmas.v *)

(* fold_scan_fusion_pair_dual - used in form7_dual_eq_form8_dual *)
Lemma fold_scan_fusion_pair_dual :
  forall (xs : list Z),
    fold_left
      (fun uv x => let '(u, v) := uv in (Z.max u (nonNegPlus v x), nonNegPlus v x))
      xs (0, 0)
    =
    (fold_left Z.max (scan_left (fun acc x => nonNegPlus acc x) xs 0) 0,
     fold_left (fun acc x => nonNegPlus acc x) xs 0).
Admitted. (* Moved from Lemmas.v *)

(* fold_left_ext - used in form7_dual_eq_form8_dual *)
Lemma fold_left_ext : forall {A B : Type} (f g : B -> A -> B) (xs : list A) (init : B),
  (forall acc x, f acc x = g acc x) ->
  fold_left f xs init = fold_left g xs init.
Admitted. (* Moved from Lemmas.v *)

(* fold_left_nonNegPlus_eq_max_suffixes - used in form5_dual_eq_form6_dual *)
Lemma fold_left_nonNegPlus_eq_max_suffixes : forall xs : list Z,
  fold_left (fun acc x => nonNegPlus acc x) xs 0 =
  nonNegMaximum_dual (map nonNegSum_dual (tails xs)).
Admitted. (* Moved from Lemmas.v *)

(* fold_left_right_rev - used in Original_Dual_Equivalence *)
Theorem fold_left_right_rev :
  forall {A B : Type} (f : A -> B -> B) (xs : list A) (init : B),
    fold_left (fun acc x => f x acc) xs init = fold_right f init (rev xs).
Admitted. (* Moved from Lemmas.v *)

(* generalised_horners_rule_dual - used in form5_dual_eq_form6_dual *)
Lemma generalised_horners_rule_dual :
  (fun xs => fold_left (fun acc x => nonNegPlus acc x) xs 0) = nonNegMaximum_dual ∘ map nonNegSum_dual ∘ tails.
Admitted. (* Moved from Lemmas.v *)

(* generalised_horners_rule_dual' - used in form5_dual_eq_form6_dual *)
Lemma generalised_horners_rule_dual' :
  nonNegMaximum_dual ∘ map (nonNegMaximum_dual ∘ map nonNegSum_dual ∘ tails) ∘ inits_rec =
  nonNegMaximum_dual ∘ map nonNegSum_dual ∘ inits_rec.
Admitted. (* Moved from Lemmas.v *)