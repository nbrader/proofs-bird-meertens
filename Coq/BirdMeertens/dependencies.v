(* dependencies.v *)
Require Import BirdMeertens.BirdMeertens.
Require Import BirdMeertens.FunctionLemmas.
Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.MonoidRLB_max.
Require Import BirdMeertens.MonoidRLB_plus.
Require Import BirdMeertens.OptionFunctions.
Require Import BirdMeertens.RealsWithLowerBound.

Require Import FreeMonoid.Category.
Require Import FreeMonoid.ExtraLemmas.
Require Import FreeMonoid.HomExampleBoolOrToNatMax1.
Require Import FreeMonoid.MonoidExampleAddAbsorbing.
Require Import FreeMonoid.MonoidExampleAddNeutral.
Require Import FreeMonoid.MonoidExampleBoolOr.
Require Import FreeMonoid.MonoidExampleEndo.
Require Import FreeMonoid.MonoidExampleFirst.
Require Import FreeMonoid.MonoidExampleLast.
Require Import FreeMonoid.MonoidExampleNatMax1.
Require Import FreeMonoid.MonoidFree.
Require Import FreeMonoid.MonoidFreeTest.
Require Import FreeMonoid.MonoidHom.
Require Import FreeMonoid.StructMagma.
Require Import FreeMonoid.StructMonoid.
Require Import FreeMonoid.StructSemigroup.
Require Import FreeMonoid.TypeCategory.

(* Add theorems/lemmas from each module to check dependencies *)
Print Assumptions RLB_sum_implementation_correctness.
Print Assumptions BirdMeertens.Lemmas.plus_distributes_over_Rmax.
Print Assumptions BirdMeertens.BirdMeertens.form1_eq_form2.
Print Assumptions BirdMeertens.BirdMeertens.form2_eq_form3.
Print Assumptions BirdMeertens.BirdMeertens.form3_eq_form4.
Print Assumptions BirdMeertens.BirdMeertens.form4_eq_form5.
Print Assumptions BirdMeertens.BirdMeertens.form4_eq_form6.
Print Assumptions BirdMeertens.Lemmas.horners_rule.
