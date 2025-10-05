Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import KadanesAlgorithm.KadanesAlgorithm.
Require Import FreeMonoid.StructSemiring.
Require Import FreeMonoid.StructMonoid.
Require Import CoqUtilLib.ListFunctions.

Open Scope Z_scope.

(*
=================================================================================
KADANE'S ALGORITHM ON ENDOMORPHISM SEMIRING
=================================================================================

This file demonstrates the generality of Kadane's algorithm by instantiating it
on the endomorphism semiring End(ℤ, +).

THEORY: If (M, +) is a commutative monoid, then the set End(M) of monoid
endomorphisms M → M forms a semiring where:
  - Addition (⊕): Pointwise addition (f ⊕ g)(x) = f(x) + g(x)
  - Multiplication (⊗): Function composition (f ∘ g)(x) = f(g(x))
  - Zero: The zero morphism zero(x) = 0
  - One: The identity morphism id(x) = x

For M = (ℤ, +), the monoid endomorphisms are exactly the linear functions
f(x) = ax (functions that preserve addition and map 0 to 0).

This is a clean, mathematically natural semiring where:
  - Kadane's algorithm finds the "best" composition of linear scalings
  - "Best" means maximizing according to some ordering on coefficients
*)

(*
=================================================================================
MONOID ENDOMORPHISMS OF (ℤ, +)
=================================================================================
*)

(* A monoid endomorphism of (ℤ, +) is a linear function f(x) = ax *)
Record EndoZ : Type := mkEndo {
  coeff : Z
}.

(* Apply endomorphism to a value *)
Definition apply_endo (f : EndoZ) (x : Z) : Z :=
  (coeff f) * x.

(* Verify this preserves the monoid structure *)
Lemma endo_preserves_zero : forall f,
  apply_endo f 0 = 0.
Proof.
  intros [a]. unfold apply_endo. simpl. lia.
Qed.

Lemma endo_preserves_add : forall f x y,
  apply_endo f (x + y) = apply_endo f x + apply_endo f y.
Proof.
  intros [a] x y. unfold apply_endo. simpl. lia.
Qed.

(*
=================================================================================
SEMIRING OPERATIONS ON End(ℤ, +)
=================================================================================
*)

(* Pointwise addition: (f + g)(x) = f(x) + g(x) = ax + bx = (a+b)x *)
Definition endo_add (f g : EndoZ) : EndoZ :=
  mkEndo (coeff f + coeff g).

(* Function composition: (f ∘ g)(x) = f(g(x)) = a(bx) = (ab)x *)
Definition endo_compose (f g : EndoZ) : EndoZ :=
  mkEndo (coeff f * coeff g).

(* Zero morphism: zero(x) = 0x = 0 *)
Definition endo_zero : EndoZ := mkEndo 0.

(* Identity morphism: id(x) = 1x = x *)
Definition endo_id : EndoZ := mkEndo 1.

(* For the semiring addition, we use regular addition (pointwise) *)
Definition endo_add_pointwise (f g : EndoZ) : EndoZ :=
  mkEndo (coeff f + coeff g).

(*
=================================================================================
SEMIRING PROPERTIES
=================================================================================
*)

(* Pointwise addition properties (addition in our semiring) *)

Lemma endo_add_assoc : forall f g h,
  endo_add_pointwise f (endo_add_pointwise g h) =
  endo_add_pointwise (endo_add_pointwise f g) h.
Proof.
  intros [a] [b] [c]. unfold endo_add_pointwise. simpl.
  f_equal. lia.
Qed.

Lemma endo_add_comm : forall f g,
  endo_add_pointwise f g = endo_add_pointwise g f.
Proof.
  intros [a] [b]. unfold endo_add_pointwise. simpl.
  f_equal. lia.
Qed.

Lemma endo_add_id_l : forall f,
  endo_add_pointwise endo_zero f = f.
Proof.
  intros [a]. unfold endo_add_pointwise, endo_zero. simpl.
  f_equal.
Qed.

Lemma endo_add_id_r : forall f,
  endo_add_pointwise f endo_zero = f.
Proof.
  intros [a]. unfold endo_add_pointwise, endo_zero. simpl.
  f_equal. lia.
Qed.

(* Composition properties (multiplication in our semiring) *)

Lemma endo_compose_assoc : forall f g h,
  endo_compose f (endo_compose g h) = endo_compose (endo_compose f g) h.
Proof.
  intros [a] [b] [c]. unfold endo_compose. simpl.
  f_equal. lia.
Qed.

Lemma endo_compose_id_l : forall f,
  endo_compose endo_id f = f.
Proof.
  intros [a]. unfold endo_compose, endo_id. simpl.
  f_equal. destruct a; reflexivity.
Qed.

Lemma endo_compose_id_r : forall f,
  endo_compose f endo_id = f.
Proof.
  intros [a]. unfold endo_compose, endo_id. simpl.
  f_equal. lia.
Qed.

(* Distributivity: composition distributes over pointwise addition *)

Lemma endo_compose_add_distr_l : forall f g h,
  endo_compose f (endo_add_pointwise g h) =
  endo_add_pointwise (endo_compose f g) (endo_compose f h).
Proof.
  intros [a] [b] [c]. unfold endo_compose, endo_add_pointwise. simpl.
  f_equal. lia.
Qed.

Lemma endo_compose_add_distr_r : forall f g h,
  endo_compose (endo_add_pointwise f g) h =
  endo_add_pointwise (endo_compose f h) (endo_compose g h).
Proof.
  intros [a] [b] [c]. unfold endo_compose, endo_add_pointwise. simpl.
  f_equal. lia.
Qed.

(* Zero annihilation *)

Lemma endo_compose_zero_l : forall f,
  endo_compose endo_zero f = endo_zero.
Proof.
  intros [a]. unfold endo_compose, endo_zero. simpl.
  reflexivity.
Qed.

Lemma endo_compose_zero_r : forall f,
  endo_compose f endo_zero = endo_zero.
Proof.
  intros [a]. unfold endo_compose, endo_zero. simpl.
  f_equal. lia.
Qed.

(*
=================================================================================
SEMIRING INSTANCE
=================================================================================
*)

#[export] Instance EndoZ_Semiring : Semiring EndoZ := {
  add_op := endo_add_pointwise;
  add_zero := endo_zero;
  add_assoc := endo_add_assoc;
  add_left_id := endo_add_id_l;
  add_right_id := endo_add_id_r;
  add_comm := endo_add_comm;

  mul_op := endo_compose;
  mul_one := endo_id;
  mul_assoc := endo_compose_assoc;
  mul_left_id := endo_compose_id_l;
  mul_right_id := endo_compose_id_r;

  mul_add_distr_l := endo_compose_add_distr_l;
  mul_add_distr_r := endo_compose_add_distr_r;

  mul_zero_l := endo_compose_zero_l;
  mul_zero_r := endo_compose_zero_r;
}.

(*
=================================================================================
KADANE'S ALGORITHM ON ENDOMORPHISMS
=================================================================================
*)

(* Kadane's algorithm for endomorphisms *)
Definition kadane_endo (fs : list EndoZ) : EndoZ :=
  gform8 fs.

(*
=================================================================================
EXAMPLE: Finding Best Endomorphism Composition
=================================================================================
*)

(* Define some example endomorphisms *)

(* f1(x) = 2x (doubling) *)
Definition f1 : EndoZ := mkEndo 2.

(* f2(x) = 3x (tripling) *)
Definition f2 : EndoZ := mkEndo 3.

(* f3(x) = -1x (negation) *)
Definition f3 : EndoZ := mkEndo (-1).

(* f4(x) = 5x (quintupling) *)
Definition f4 : EndoZ := mkEndo 5.

(* f5(x) = -2x (double and negate) *)
Definition f5 : EndoZ := mkEndo (-2).

(*
The algorithm finds the "best" contiguous subsequence of endomorphism
compositions, where "best" is determined by the semiring addition operation
(pointwise addition of coefficients).

Since composition multiplies coefficients, this demonstrates how Kadane's
algorithm works on the endomorphism semiring End(ℤ, +).
*)

(* Compute the best composition from lists of endomorphisms *)
Compute kadane_endo [f1; f2; f3].      (* Combines all compositions using pointwise addition *)
Compute kadane_endo [f1; f2; f4; f5].  (* Result depends on semiring sum of all segments *)
Compute kadane_endo [f3; f5; f1].      (* Demonstrates endomorphism algebra *)

(*
=================================================================================
CORRECTNESS
=================================================================================
*)

(* The main correctness theorem from KadanesAlgorithm.v applies directly *)
Check @Generalized_Kadane_Correctness EndoZ EndoZ_Semiring.

(*
Theorem: For any list of endomorphisms fs,
  gform8 fs = gform1 fs

This means the efficient implementation (gform8) using scan and fold
correctly computes the same result as the specification (gform1) which
examines all segments.

In our case:
- gform1: semiring sum over all segments of (product of segment)
         = combining all contiguous subsequence compositions via pointwise addition
- gform8: efficient scan-fold implementation (Kadane's algorithm)
*)

(*
=================================================================================
INTERPRETATION
=================================================================================

What does this mean practically?

Given a sequence of linear endomorphisms [f1, f2, ..., fn], Kadane's
algorithm combines all contiguous subsequences using the semiring operations:
- Composition (⊗) for combining elements within a subsequence
- Pointwise addition (⊕) for combining results across different subsequences

For endomorphisms f(x) = ax, composition gives (f ∘ g)(x) = (a·b)x, so
the composition of a subsequence yields a single endomorphism whose
coefficient is the product of the individual coefficients.

The semiring addition then combines these products via pointwise addition:
if we have compositions with coefficients c₁ and c₂, their sum has
coefficient (c₁ + c₂).

This demonstrates that the endomorphism semiring is a natural and clean
setting for Kadane's algorithm, arising from fundamental category theory
(endomorphisms of a monoid).
*)
