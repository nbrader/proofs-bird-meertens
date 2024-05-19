(* dependencies.v *)
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
Print Assumptions BirdMeertens.Lemmas.plus_distributes_over_Rmax.
Print Assumptions BirdMeertens.Lemmas.horners_rule.
