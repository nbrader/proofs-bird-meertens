(* Major Lemmas - Immediate Dependencies of BirdMeertens.v *)
(* This file contains theorems that BirdMeertens.v depends on directly *)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import BirdMeertens.Lemmas.
Require Import CoqUtilLib.ListFunctions.

Require Import Coq.ZArith.Int.
Require Import Coq.ZArith.BinInt.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

(* All the definitions and basic lemmas are imported from Lemmas.v *)
(* This file contains only the major theorems that BirdMeertens.v directly uses *)

(* Re-export the immediate dependencies that BirdMeertens.v needs *)

(* These lemmas are direct dependencies from the TGF analysis: *)
(* - map_promotion (used in form2_eq_form3) *)
(* - fold_promotion (used in form3_eq_form4) *)
(* - fold_promotion_dual (used in form3_dual_eq_form4_dual) *)
(* - nonNegPlus_comm (used in form7_eq_form8) *)
(* - generalised_horners_rule (used in form5_eq_form6) *)
(* - tails_rec_equiv_ext (used in form5_eq_form6) *)
(* - scan_right_tails_rec_fold (used in form6_eq_form7) *)
(* - fold_scan_fusion_pair (used in form7_eq_form8) *)
(* - maxSoFarAndPreviousSum (used in form7_eq_form8) *)
(* - fold_right_ext (used in form7_eq_form8) *)
(* - scan_left_inits_rec_fold (used in form6_dual_eq_form7_dual) *)
(* - fold_scan_fusion_pair_dual (used in form7_dual_eq_form8_dual) *)
(* - maxSoFarAndPreviousSum_dual (used in form7_dual_eq_form8_dual) *)
(* - fold_left_ext (used in form7_dual_eq_form8_dual) *)
(* - fold_left_nonNegPlus_eq_max_suffixes (used in form5_dual_eq_form6_dual) *)
(* - fold_left_right_rev (used in Original_Dual_Equivalence) *)

(* Note: All these lemmas are already defined and proven in Lemmas.v *)
(* They are automatically available through the import *)