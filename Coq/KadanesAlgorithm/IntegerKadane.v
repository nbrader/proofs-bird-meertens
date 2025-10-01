(*
  Test: Can we instantiate gform1-gform6 with the integer semiring (Z, +, ×)?

  This should work because Horner's rule applies to ANY semiring.
*)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CoqUtilLib.ListFunctions.
Require Import FreeMonoid.StructSemiring.
Require Import FreeMonoid.SemiringLemmas.
Require Import KadanesAlgorithm.KadanesAlgorithm.
Import ListNotations.

Open Scope Z_scope.

(* Integer semiring: (Z, +, ×, 0, 1) *)
#[export] Instance ZSemiring : Semiring Z := {
  add_op := Z.add;
  add_zero := 0;
  add_assoc := Z.add_assoc;
  add_left_id := Z.add_0_l;
  add_right_id := Z.add_0_r;
  add_comm := Z.add_comm;

  mul_op := Z.mul;
  mul_one := 1;
  mul_assoc := Z.mul_assoc;
  mul_left_id := Z.mul_1_l;
  mul_right_id := Z.mul_1_r;

  mul_add_distr_l := Z.mul_add_distr_l;
  mul_add_distr_r := Z.mul_add_distr_r;
  mul_zero_l := Z.mul_0_l;
  mul_zero_r := Z.mul_0_r
}.

(* Test: gform1 through gform6 should all work *)
Check @gform1 Z ZSemiring.
Check @gform2 Z ZSemiring.
Check @gform3 Z ZSemiring.
Check @gform4 Z ZSemiring.
Check @gform5 Z ZSemiring.
Check @gform6 Z ZSemiring.

(* The equivalences gform1-gform5 should work *)
Check @gform1_eq_gform2 Z ZSemiring.
Check @gform2_eq_gform3 Z ZSemiring.
Check @gform3_eq_gform4 Z ZSemiring.
Check @gform4_eq_gform5 Z ZSemiring.

(* What about gform5 = gform6? This should work via Horner's rule! *)
Theorem integer_gform5_eq_gform6 : @gform5 Z _ = @gform6 Z _.
Proof.
  unfold gform5, gform6.
  apply functional_extensionality; intro xs.
  unfold compose.
  f_equal.
  apply map_ext.
  intros a.
  unfold semiring_sum, semiring_product.

  (* This is exactly what Horner's rule gives us *)
  pose proof (@generalised_horners_rule_right Z _) as HR.
  rewrite (equal_f HR a).
  unfold compose.
  reflexivity.
Qed.

(* So the integer semiring DOES satisfy the gform5 = gform6 step! *)
(* This means the KadaneSemiring class might be unnecessarily restrictive. *)

(*
CONCLUSION:

The gform5 → gform6 transition works for ANY semiring via Horner's rule.
This includes the integer semiring (Z, +, ×, 0, 1).

The KadaneSemiring class in KadanesAlgorithm.v appears to be incorrectly formulated:
- It includes kadane_horner_property which is NOT equivalent to Horner's rule
- It includes mul_one_add_absorb which is very restrictive
- These properties are not needed for gform5 → gform6

The actual Horner's rule (from FreeMonoid.SemiringLemmas) states:
  fold_right (λx y. (x ⊗ y) ⊕ 𝟏) 𝟏 xs =
  fold_right (⊕) 𝟎 (map (fold_right (⊗) 𝟏) (inits xs))

This directly gives us gform5 = gform6 for any semiring.

Therefore, gform1 through gform6 can be proven equivalent for ALL semirings.
The restrictive KadaneSemiring class may only be needed for later steps (gform7, gform8).
*)
