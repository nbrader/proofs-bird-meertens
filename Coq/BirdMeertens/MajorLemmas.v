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

(* Import all basic definitions from Lemmas.v *)
(* Re-export the major lemmas that are immediate dependencies: *)

(* map_promotion - used in form2_eq_form3 *)
(* fold_promotion - used in form3_eq_form4 *)
(* nonNegPlus_comm - used in form7_eq_form8 *)
(* generalised_horners_rule - used in form5_eq_form6 *)
(* fold_scan_fusion_pair - used in form7_eq_form8 *)
(* maxSoFarAndPreviousSum - used in form7_eq_form8 *)
(* fold_right_ext - used in form7_eq_form8 *)

(* All dual versions for the dual form theorems *)
(* fold_promotion_dual - used in form3_dual_eq_form4_dual *)
(* fold_scan_fusion_pair_dual - used in form7_dual_eq_form8_dual *)
(* maxSoFarAndPreviousSum_dual - used in form7_dual_eq_form8_dual *)
(* fold_left_ext - used in form7_dual_eq_form8_dual *)
(* fold_left_nonNegPlus_eq_max_suffixes - used in form5_dual_eq_form6_dual *)

(* fold_left_right_rev - used in Original_Dual_Equivalence *)

(* Note: tails_rec_equiv_ext, scan_right_tails_rec_fold, scan_left_inits_rec_fold *)
(* are defined in CoqUtilLib.ListFunctions and imported automatically *)

(* All these lemmas are already defined and proven in Lemmas.v *)
(* They are automatically available through the import *)
(* This file serves as a clear documentation of what BirdMeertens.v uses directly *)