(* Major Lemmas - Immediate Dependencies of BirdMeertens.v *)
(* This file re-exports the immediate dependencies that BirdMeertens.v uses directly *)

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

(* ===== DOCUMENTATION OF IMMEDIATE DEPENDENCIES ===== *)
(* The following theorems are the immediate dependencies of BirdMeertens.v *)
(* They are available through the export of Lemmas.v above *)

(* PRIMARY FORM DEPENDENCIES: *)
(* 1. map_promotion - used in form2_eq_form3 *)
(* 2. fold_promotion - used in form3_eq_form4 *)
(* 3. nonNegPlus_comm - used in form7_eq_form8 *)
(* 4. fold_scan_fusion_pair - used in form7_eq_form8 *)
(* 5. generalised_horners_rule - used in form5_eq_form6 *)
(* 6. generalised_horners_rule' - used in form5_eq_form6 *)
(* 7. fold_right_ext - used in form7_eq_form8 *)

(* DUAL FORM DEPENDENCIES: *)
(* 8. fold_promotion_dual - used in form3_dual_eq_form4_dual *)
(* 9. fold_scan_fusion_pair_dual - used in form7_dual_eq_form8_dual *)
(* 10. fold_left_ext - used in form7_dual_eq_form8_dual *)
(* 11. fold_left_nonNegPlus_eq_max_suffixes - used in form5_dual_eq_form6_dual *)
(* 12. fold_left_right_rev - used in Original_Dual_Equivalence *)
(* 13. generalised_horners_rule_dual - used in form5_dual_eq_form6_dual *)
(* 14. generalised_horners_rule_dual' - used in form5_dual_eq_form6_dual *)

(* HELPER DEFINITIONS: *)
(* - maxSoFarAndPreviousSum - used in form7_eq_form8 *)
(* - maxSoFarAndPreviousSum_dual - used in form7_dual_eq_form8_dual *)

(* UTILITY LIBRARY FUNCTIONS: *)
(* - tails_rec_equiv_ext - used in form5_eq_form6 *)
(* - scan_right_tails_rec_fold - used in form6_eq_form7 *)
(* - scan_left_inits_rec_fold - used in form6_dual_eq_form7_dual *)

(* All these theorems and definitions are implemented in Lemmas.v *)
(* and utility functions in CoqUtilLib.ListFunctions *)

(* This file serves as the clean interface that documents exactly *)
(* what BirdMeertens.v depends on immediately, separating it from *)
(* the indirect dependencies that these theorems themselves use *)

(* The reorganization achieves: *)
(* - BirdMeertens.v → MajorLemmas.v (immediate deps interface) *)
(* - MajorLemmas.v → Lemmas.v (theorem implementations) *)
(* - Lemmas.v → indirect dependencies only *)
(* - Extra.v → unused theorems *)