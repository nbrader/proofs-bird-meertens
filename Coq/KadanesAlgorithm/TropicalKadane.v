Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

(* Import the generalized framework *)
Require Import KadanesAlgorithm.KadanesAlgorithm.
Require Import FreeMonoid.StructSemiring.
Require Import CoqUtilLib.ListFunctions.

(*
=================================================================================
KADANE'S ALGORITHM FOR MAXIMUM SUBARRAY VIA TROPICAL SEMIRING
=================================================================================

This file instantiates the generalized Kadane's algorithm with the tropical
semiring to derive the traditional maximum subarray algorithm.

TROPICAL SEMIRING:
- Elements: Extended integers (ℤ ∪ {-∞})
- Addition ⊕: max operation
- Multiplication ⊗: regular addition
- Additive identity 𝟘: -∞
- Multiplicative identity 𝟙: 0

INTERPRETATION:
- semiring_sum xs = max(xs) = maximum element
- semiring_product xs = sum(xs) = sum of elements
- gform1 xs = max { sum(seg) | seg ∈ segs(xs) } = maximum subarray sum
*)

(*
=================================================================================
EXTENDED INTEGERS WITH NEGATIVE INFINITY
=================================================================================
*)

Inductive ExtZ : Type :=
  | NegInf : ExtZ
  | Finite : Z -> ExtZ.

(* Comparison *)
Definition extZ_le (x y : ExtZ) : Prop :=
  match x, y with
  | NegInf, _ => True
  | _, NegInf => False
  | Finite a, Finite b => (a <= b)%Z
  end.

(* Tropical addition = max *)
Definition tropical_add (x y : ExtZ) : ExtZ :=
  match x, y with
  | NegInf, z => z
  | z, NegInf => z
  | Finite a, Finite b => Finite (Z.max a b)
  end.

(* Tropical multiplication = regular addition *)
Definition tropical_mul (x y : ExtZ) : ExtZ :=
  match x, y with
  | NegInf, _ => NegInf
  | _, NegInf => NegInf
  | Finite a, Finite b => Finite (a + b)
  end.

(* Identities *)
Definition tropical_zero : ExtZ := NegInf.
Definition tropical_one : ExtZ := Finite 0.

(*
=================================================================================
TROPICAL SEMIRING INSTANCE
=================================================================================
*)

(* Prove all semiring axioms for tropical semiring *)

Lemma tropical_add_assoc : forall x y z : ExtZ,
  tropical_add x (tropical_add y z) = tropical_add (tropical_add x y) z.
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  rewrite Z.max_assoc. reflexivity.
Qed.

Lemma tropical_add_comm : forall x y : ExtZ,
  tropical_add x y = tropical_add y x.
Proof.
  intros x y.
  destruct x, y; simpl; try reflexivity.
  rewrite Z.max_comm. reflexivity.
Qed.

Lemma tropical_add_left_id : forall x : ExtZ,
  tropical_add tropical_zero x = x.
Proof.
  intro x. destruct x; reflexivity.
Qed.

Lemma tropical_add_right_id : forall x : ExtZ,
  tropical_add x tropical_zero = x.
Proof.
  intro x. destruct x; reflexivity.
Qed.

Lemma tropical_mul_assoc : forall x y z : ExtZ,
  tropical_mul x (tropical_mul y z) = tropical_mul (tropical_mul x y) z.
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  rewrite Z.add_assoc. reflexivity.
Qed.

Lemma tropical_mul_left_id : forall x : ExtZ,
  tropical_mul tropical_one x = x.
Proof.
  intro x. destruct x; simpl; reflexivity.
Qed.

Lemma tropical_mul_right_id : forall x : ExtZ,
  tropical_mul x tropical_one = x.
Proof.
  intro x. destruct x; simpl; try reflexivity.
  f_equal. apply Z.add_0_r.
Qed.

Lemma tropical_mul_left_distr : forall x y z : ExtZ,
  tropical_mul x (tropical_add y z) = tropical_add (tropical_mul x y) (tropical_mul x z).
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  rewrite Z.add_max_distr_l. reflexivity.
Qed.

Lemma tropical_mul_right_distr : forall x y z : ExtZ,
  tropical_mul (tropical_add x y) z = tropical_add (tropical_mul x z) (tropical_mul y z).
Proof.
  intros x y z.
  destruct x, y, z; simpl; try reflexivity.
  rewrite Z.add_max_distr_r. reflexivity.
Qed.

Lemma tropical_mul_left_absorb : forall x : ExtZ,
  tropical_mul tropical_zero x = tropical_zero.
Proof.
  intro x. destruct x; reflexivity.
Qed.

Lemma tropical_mul_right_absorb : forall x : ExtZ,
  tropical_mul x tropical_zero = tropical_zero.
Proof.
  intro x. destruct x; reflexivity.
Qed.

(* Create the semiring instance *)
#[export] Instance TropicalSemiring : Semiring ExtZ := {
  add_op := tropical_add;
  mul_op := tropical_mul;
  add_zero := tropical_zero;
  mul_one := tropical_one;

  add_assoc := tropical_add_assoc;
  add_comm := tropical_add_comm;
  add_left_id := tropical_add_left_id;
  add_right_id := tropical_add_right_id;

  mul_assoc := tropical_mul_assoc;
  mul_left_id := tropical_mul_left_id;
  mul_right_id := tropical_mul_right_id;

  mul_add_distr_l := tropical_mul_left_distr;
  mul_add_distr_r := tropical_mul_right_distr;

  mul_zero_l := tropical_mul_left_absorb;
  mul_zero_r := tropical_mul_right_absorb;
}.

(*
=================================================================================
INSTANTIATION OF KADANE'S ALGORITHM
=================================================================================
*)

(* Maximum subarray sum using the generalized framework *)
Definition max_subarray_sum (xs : list ExtZ) : ExtZ :=
  gform8 xs.

(* The specification *)
Definition max_subarray_spec (xs : list ExtZ) : ExtZ :=
  gform1 xs.

(* Correctness follows immediately from the general theorem *)
Theorem max_subarray_correct : max_subarray_sum = max_subarray_spec.
Proof.
  unfold max_subarray_sum, max_subarray_spec.
  symmetry.
  apply Generalized_Kadane_Correctness.
Qed.

(*
=================================================================================
CONCRETE ALGORITHM FOR INTEGER LISTS
=================================================================================
*)

(* Lift integer lists to ExtZ *)
Definition lift_Z (xs : list Z) : list ExtZ :=
  map Finite xs.

(* Extract result (assumes result is finite) *)
Definition extract_finite (x : ExtZ) : option Z :=
  match x with
  | NegInf => None
  | Finite z => Some z
  end.

(* Maximum subarray sum for integer lists *)
Definition kadane_algorithm (xs : list Z) : option Z :=
  extract_finite (max_subarray_sum (lift_Z xs)).

(*
=================================================================================
INTERPRETATION AND EXAMPLES
=================================================================================

The generalized gform8 for the tropical semiring becomes:

  max_subarray_sum xs =
    fst (fold_right step (max one zero, one) xs)

  where step x (u, v) =
    let w = max (x + v) one in
    (max w u, w)

This is exactly the traditional Kadane's algorithm!

- u tracks the global maximum
- v tracks the best sum ending at current position
- w = max(x + v, 0) is the best sum including current element
- max w u updates the global maximum

EXAMPLE: [2, -1, 3, -2, 1]

Initial: u = max(-∞, 0) = 0, v = 0
Step 1 (x=2):  w = max(2+0, 0) = 2,  u = max(2, 0) = 2
Step 2 (x=-1): w = max(-1+2, 0) = 1, u = max(1, 2) = 2
Step 3 (x=3):  w = max(3+1, 0) = 4,  u = max(4, 2) = 4
Step 4 (x=-2): w = max(-2+4, 0) = 2, u = max(2, 4) = 4
Step 5 (x=1):  w = max(1+2, 0) = 3,  u = max(3, 4) = 4

Result: 4 (subarray [2, -1, 3])
*)
