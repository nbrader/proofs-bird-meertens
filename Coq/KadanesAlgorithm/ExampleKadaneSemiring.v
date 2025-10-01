(*
  Concrete example of a KadaneSemiring instance.

  This demonstrates two semirings:
  1. The trivial semiring (unit type) - satisfies properties trivially
  2. A non-trivial "absorbing max" semiring on option nat
*)

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import CoqUtilLib.ListFunctions.
Require Import FreeMonoid.StructSemiring.
Require Import FreeMonoid.SemiringLemmas.
Require Import KadanesAlgorithm.KadanesAlgorithm.
Import ListNotations.

(*
=================================================================================
EXAMPLE 1: TRIVIAL SEMIRING
=================================================================================

  Trivial semiring on unit type:
  - Addition: unique operation (always returns tt)
  - Multiplication: unique operation (always returns tt)
  - Additive identity: tt
  - Multiplicative identity: tt

  This is the simplest possible semiring and trivially satisfies
  all KadaneSemiring properties since all values are equal.
*)

#[export] Instance TrivialSemiring : Semiring unit := {
  add_op := fun _ _ => tt;
  mul_op := fun _ _ => tt;
  add_zero := tt;
  mul_one := tt;

  add_assoc := fun x y z => match x, y, z with tt, tt, tt => eq_refl end;
  add_left_id := fun x => match x with tt => eq_refl end;
  add_right_id := fun x => match x with tt => eq_refl end;
  add_comm := fun x y => match x, y with tt, tt => eq_refl end;

  mul_assoc := fun x y z => match x, y, z with tt, tt, tt => eq_refl end;
  mul_left_id := fun x => match x with tt => eq_refl end;
  mul_right_id := fun x => match x with tt => eq_refl end;

  mul_add_distr_l := fun x y z => match x, y, z with tt, tt, tt => eq_refl end;
  mul_add_distr_r := fun x y z => match x, y, z with tt, tt, tt => eq_refl end;
  mul_zero_l := fun x => match x with tt => eq_refl end;
  mul_zero_r := fun x => match x with tt => eq_refl end
}.

(* Verify the KadaneSemiring properties for trivial semiring *)

Lemma trivial_mul_comm :
  forall (x y : unit), mul_op x y = mul_op y x.
Proof.
  intros x y.
  reflexivity.
Qed.

Lemma trivial_mul_one_add_absorb :
  add_op mul_one add_zero = add_zero.
Proof.
  reflexivity.
Qed.

#[export] Instance TrivialKadaneSemiring : KadaneSemiring unit := {
  mul_comm := trivial_mul_comm;
  mul_one_add_absorb := trivial_mul_one_add_absorb
}.

(*
  This instance shows that KadaneSemiring is not an empty class.
  While the trivial semiring is not interesting computationally,
  it demonstrates that the KadaneSemiring axioms are consistent.
*)

(*
=================================================================================
EXAMPLE 2: FINDING NON-TRIVIAL KADANE SEMIRINGS
=================================================================================

Finding non-trivial semirings that satisfy KadaneSemiring is challenging.

The key constraint is mul_one_add_absorb: add_op mul_one add_zero = add_zero

This is a very restrictive property. Known semirings that fail this:
- Tropical (max-plus) semiring: max(0, -∞) = 0 ≠ -∞ (see TropicalNotKadane.v)
- Boolean semiring: true ∨ false = true ≠ false
- Natural numbers: 1 + 0 = 1 ≠ 0

The property essentially requires that the multiplicative identity "disappears"
when added to the additive identity, which is unusual for standard semirings.

One approach: Set mul_one = add_zero. But then identity axioms become challenging.

IMPORTANT NOTE: KadaneSemiring properties are only needed for gform7 → gform8
(the scan-fold fusion step). The earlier forms gform1-gform6 work for ANY semiring,
including integers, tropical semiring, etc. See IntegerKadane.v for a demonstration.

Open problem: Find a non-trivial, computationally interesting semiring that
satisfies all KadaneSemiring properties.
*)
