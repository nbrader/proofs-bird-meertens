Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.

(* Import the generalized framework *)
Require Import KadanesAlgorithm.KadanesAlgorithm.
Require Import FreeMonoid.StructSemiring.
Require Import CoqUtilLib.ListFunctions.

(*
=================================================================================
KADANE'S ALGORITHM FOR NATURAL NUMBERS
=================================================================================

This file instantiates the generalized Kadane's algorithm with the standard
natural number semiring (ℕ, +, *, 0, 1).

NATURAL NUMBER SEMIRING:
- Elements: Natural numbers ℕ
- Addition ⊕: regular addition (+)
- Multiplication ⊗: regular multiplication ( * )
- Additive identity 𝟘: 0
- Multiplicative identity 𝟙: 1

INTERPRETATION:
- semiring_sum xs = sum(xs) = sum of all elements
- semiring_product xs = product(xs) = product of all elements
- gform1 xs = sum { product(seg) | seg ∈ segs(xs) } = sum of all subarray products

This is the standard semiring of natural numbers, different from the tropical
semiring used for maximum subarray problems.
*)

(*
=================================================================================
NATURAL NUMBER SEMIRING INSTANCE
=================================================================================
*)

(* The operations are standard *)
Definition nat_add := Nat.add.
Definition nat_mul := Nat.mul.
Definition nat_zero := 0.
Definition nat_one := 1.

(* Semiring axioms for (ℕ, +, *, 0, 1) *)

Lemma nat_add_assoc : forall x y z : nat,
  nat_add x (nat_add y z) = nat_add (nat_add x y) z.
Proof.
  intros. unfold nat_add. apply Nat.add_assoc.
Qed.

Lemma nat_add_comm : forall x y : nat,
  nat_add x y = nat_add y x.
Proof.
  intros. unfold nat_add. apply Nat.add_comm.
Qed.

Lemma nat_add_left_id : forall x : nat,
  nat_add nat_zero x = x.
Proof.
  intro x. unfold nat_add, nat_zero. apply Nat.add_0_l.
Qed.

Lemma nat_add_right_id : forall x : nat,
  nat_add x nat_zero = x.
Proof.
  intro x. unfold nat_add, nat_zero. apply Nat.add_0_r.
Qed.

Lemma nat_mul_assoc : forall x y z : nat,
  nat_mul x (nat_mul y z) = nat_mul (nat_mul x y) z.
Proof.
  intros. unfold nat_mul. apply Nat.mul_assoc.
Qed.

Lemma nat_mul_left_id : forall x : nat,
  nat_mul nat_one x = x.
Proof.
  intro x. unfold nat_mul, nat_one. apply Nat.mul_1_l.
Qed.

Lemma nat_mul_right_id : forall x : nat,
  nat_mul x nat_one = x.
Proof.
  intro x. unfold nat_mul, nat_one. apply Nat.mul_1_r.
Qed.

Lemma nat_mul_add_distr_l : forall x y z : nat,
  nat_mul x (nat_add y z) = nat_add (nat_mul x y) (nat_mul x z).
Proof.
  intros x y z.
  unfold nat_mul, nat_add.
  apply Nat.mul_add_distr_l.
Qed.

Lemma nat_mul_add_distr_r : forall x y z : nat,
  nat_mul (nat_add x y) z = nat_add (nat_mul x z) (nat_mul y z).
Proof.
  intros x y z.
  unfold nat_mul, nat_add.
  apply Nat.mul_add_distr_r.
Qed.

Lemma nat_mul_zero_l : forall x : nat,
  nat_mul nat_zero x = nat_zero.
Proof.
  intro x. unfold nat_mul, nat_zero. apply Nat.mul_0_l.
Qed.

Lemma nat_mul_zero_r : forall x : nat,
  nat_mul x nat_zero = nat_zero.
Proof.
  intro x. unfold nat_mul, nat_zero. apply Nat.mul_0_r.
Qed.

(* Create the semiring instance *)
#[export] Instance NatSemiring : Semiring nat := {
  add_op := nat_add;
  mul_op := nat_mul;
  add_zero := nat_zero;
  mul_one := nat_one;

  add_assoc := nat_add_assoc;
  add_comm := nat_add_comm;
  add_left_id := nat_add_left_id;
  add_right_id := nat_add_right_id;

  mul_assoc := nat_mul_assoc;
  mul_left_id := nat_mul_left_id;
  mul_right_id := nat_mul_right_id;

  mul_add_distr_l := nat_mul_add_distr_l;
  mul_add_distr_r := nat_mul_add_distr_r;

  mul_zero_l := nat_mul_zero_l;
  mul_zero_r := nat_mul_zero_r;
}.

(*
=================================================================================
INSTANTIATION OF KADANE'S ALGORITHM
=================================================================================
*)

(* Sum of subarray products for natural numbers *)
Definition nat_sum_subarray_products (xs : list nat) : nat :=
  gform8 xs.

(* The specification *)
Definition nat_sum_subarray_products_spec (xs : list nat) : nat :=
  gform1 xs.

(* Correctness follows immediately from the general theorem *)
Theorem nat_sum_subarray_products_correct :
  nat_sum_subarray_products = nat_sum_subarray_products_spec.
Proof.
  unfold nat_sum_subarray_products, nat_sum_subarray_products_spec.
  symmetry.
  apply Generalized_Kadane_Correctness.
Qed.

(*
=================================================================================
INTERPRETATION AND EXAMPLES
=================================================================================

The generalized gform8 for the standard natural number semiring computes:
  sum { product(seg) | seg ∈ segs(xs) }

That is, it sums the products of all contiguous subarrays.

The algorithm becomes:

  nat_sum_subarray_products xs =
    fst (fold_right step (1, 1) xs)

  where step x (u, v) =
    let w = x * v + 1 in
    (u + w, w)

This uses the horner_op for the natural number semiring:
  horner_op x y = x * y + 1

EXAMPLE: [2, 3]

Subarrays and their products:
- [2]: product = 2
- [3]: product = 3
- [2,3]: product = 2*3 = 6

Sum of products: 2 + 3 + 6 = 11

Let's trace the algorithm:
Initial: u = 1, v = 1

Step 1 (x=2):
  w = 2 * 1 + 1 = 3
  u = 3 + 1 = 4 (incorrect - need to check)
  v = 3

Actually, let me reconsider the interpretation...

For (ℕ, +, *, 0, 1):
- semiring_sum = fold with + starting at 0 = sum
- semiring_product = fold with * starting at 1 = product
- gform1 = sum of products of all subarrays

EXAMPLE: [2, 3]
- Subarrays: [], [2], [3], [2,3]
- Products: 1, 2, 3, 6
- Sum: 1 + 2 + 3 + 6 = 12

Note: Empty subarray has product 1 (multiplicative identity).
*)

(*
=================================================================================
COMPARISON WITH TROPICAL SEMIRING
=================================================================================

The standard natural number semiring (ℕ, +, *, 0, 1) computes:
  sum { product(seg) | seg ∈ segs(xs) }
  = sum of all subarray products

The tropical semiring (ExtZ, max, +, -∞, 0) computes:
  max { sum(seg) | seg ∈ segs(xs) }
  = maximum subarray sum

These are DIFFERENT problems solved by the SAME algorithmic framework!

This demonstrates the power of the semiring abstraction:
- Same algorithm structure (gform1 through gform8)
- Same proof of correctness (Generalized_Kadane_Correctness)
- Different computational interpretation depending on the semiring

The framework is truly general and type-safe.
*)
