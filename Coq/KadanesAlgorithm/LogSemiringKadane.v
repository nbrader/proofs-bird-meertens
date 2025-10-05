Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Require Import KadanesAlgorithm.KadanesAlgorithm.
Require Import FreeMonoid.StructSemiring.
Require Import CoqUtilLib.ListFunctions.

Open Scope Z_scope.

(*
=================================================================================
KADANE'S ALGORITHM ON LOG-SEMIRING
=================================================================================

This file demonstrates Kadane's algorithm on the log-semiring, where:

- ADDITION (⊕) is log-sum-exp: log(e^x + e^y) ≈ max(x,y)
- MULTIPLICATION (⊗) is regular addition: x + y
- Zero: -∞ (log of 0)
- One: 0 (log of 1)

The log-semiring is widely used in machine learning and probability theory
for numerical stability. Instead of multiplying probabilities (which can
underflow), we work in log-space where multiplication becomes addition.

For numerical stability, log-sum-exp is often approximated as max in practice:
  log(e^x + e^y) = max(x,y) + log(1 + e^(-|x-y|))
                 ≈ max(x,y)  when |x-y| is large

This gives us the tropical semiring (max, +) as the approximation of the
true log-semiring. We use this approximation for simplicity.

Kadane's algorithm on this semiring finds the maximum sum over all contiguous
subsequences, which in probability space corresponds to finding the subsequence
with maximum product of probabilities.
*)

(*
=================================================================================
LOG-SEMIRING ELEMENTS
=================================================================================
*)

(* Extended integers: Z ∪ {-∞} *)
Inductive ExtZ : Type :=
  | NegInf : ExtZ
  | Finite : Z -> ExtZ.

(* Elements in log-space *)
Definition LogVal := ExtZ.

(*
=================================================================================
LOG-SEMIRING OPERATIONS
=================================================================================
*)

(* Log-sum-exp approximated as max (tropical semiring) *)
Definition log_add (x y : LogVal) : LogVal :=
  match x, y with
  | NegInf, _ => y
  | _, NegInf => x
  | Finite zx, Finite zy => Finite (Z.max zx zy)
  end.

(* Addition in log-space (= multiplication in probability space) *)
Definition log_mult (x y : LogVal) : LogVal :=
  match x, y with
  | NegInf, _ => NegInf
  | _, NegInf => NegInf
  | Finite zx, Finite zy => Finite (zx + zy)
  end.

(* Zero element: -∞ (log of 0) *)
Definition log_zero : LogVal := NegInf.

(* One element: 0 (log of 1) *)
Definition log_one : LogVal := Finite 0.

(*
=================================================================================
SEMIRING PROPERTIES
=================================================================================
*)

(* Addition properties *)

Lemma log_add_comm : forall x y,
  log_add x y = log_add y x.
Proof.
  intros [|zx] [|zy]; simpl; try reflexivity.
  f_equal. apply Z.max_comm.
Qed.

Lemma log_add_assoc : forall x y z,
  log_add x (log_add y z) = log_add (log_add x y) z.
Proof.
  intros [|zx] [|zy] [|zz]; simpl; try reflexivity.
  f_equal. apply Z.max_assoc.
Qed.

Lemma log_add_id_l : forall x,
  log_add log_zero x = x.
Proof.
  intros [|zx]; simpl; reflexivity.
Qed.

Lemma log_add_id_r : forall x,
  log_add x log_zero = x.
Proof.
  intros [|zx]; simpl; reflexivity.
Qed.

(* Multiplication properties *)

Lemma log_mult_assoc : forall x y z,
  log_mult x (log_mult y z) = log_mult (log_mult x y) z.
Proof.
  intros [|zx] [|zy] [|zz]; simpl; try reflexivity.
  f_equal. lia.
Qed.

Lemma log_mult_id_l : forall x,
  log_mult log_one x = x.
Proof.
  intros [|zx]; simpl; reflexivity.
Qed.

Lemma log_mult_id_r : forall x,
  log_mult x log_one = x.
Proof.
  intros [|zx]; simpl; try reflexivity.
  f_equal. apply Z.add_0_r.
Qed.

(* Distributivity *)

Lemma log_mult_add_distr_l : forall x y z,
  log_mult x (log_add y z) = log_add (log_mult x y) (log_mult x z).
Proof.
  intros [|zx] [|zy] [|zz]; simpl; try reflexivity.
  f_equal. lia.
Qed.

Lemma log_mult_add_distr_r : forall x y z,
  log_mult (log_add x y) z = log_add (log_mult x z) (log_mult y z).
Proof.
  intros [|zx] [|zy] [|zz]; simpl; try reflexivity.
  f_equal. lia.
Qed.

(* Zero annihilates *)

Lemma log_mult_zero_l : forall x,
  log_mult log_zero x = log_zero.
Proof.
  intros [|zx]; simpl; reflexivity.
Qed.

Lemma log_mult_zero_r : forall x,
  log_mult x log_zero = log_zero.
Proof.
  intros [|zx]; simpl; reflexivity.
Qed.

(*
=================================================================================
SEMIRING INSTANCE
=================================================================================
*)

#[export] Instance LogVal_Semiring : Semiring LogVal := {
  add_op := log_add;
  add_zero := log_zero;
  add_assoc := log_add_assoc;
  add_left_id := log_add_id_l;
  add_right_id := log_add_id_r;
  add_comm := log_add_comm;

  mul_op := log_mult;
  mul_one := log_one;
  mul_assoc := log_mult_assoc;
  mul_left_id := log_mult_id_l;
  mul_right_id := log_mult_id_r;

  mul_add_distr_l := log_mult_add_distr_l;
  mul_add_distr_r := log_mult_add_distr_r;

  mul_zero_l := log_mult_zero_l;
  mul_zero_r := log_mult_zero_r;
}.

(*
=================================================================================
KADANE'S ALGORITHM ON LOG-SEMIRING
=================================================================================
*)

(* Kadane's algorithm in log-space *)
Definition kadane_log (vals : list LogVal) : LogVal :=
  gform8 vals.

(*
=================================================================================
EXAMPLES
=================================================================================
*)

(* Example log values (e.g., log probabilities) *)
Definition v1 : LogVal := Finite (-3).   (* log(p1) ≈ -3 *)
Definition v2 : LogVal := Finite (-1).   (* log(p2) ≈ -1 *)
Definition v3 : LogVal := Finite (-5).   (* log(p3) ≈ -5 *)
Definition v4 : LogVal := Finite (-2).   (* log(p4) ≈ -2 *)
Definition v5 : LogVal := Finite (-8).   (* log(p5) ≈ -8 *)

(* Compute best subsequence in log-space *)
Compute kadane_log [v1; v2; v3; v4; v5].

(* Information-theoretic values (positive log values) *)
Definition i1 : LogVal := Finite 2.     (* 2 units *)
Definition i2 : LogVal := Finite 3.     (* 3 units *)
Definition i3 : LogVal := Finite (-1).  (* -1 unit *)
Definition i4 : LogVal := Finite 1.     (* 1 unit *)

Compute kadane_log [i1; i2; i3; i4].

(* Mixed positive and negative *)
Definition m1 : LogVal := Finite 5.
Definition m2 : LogVal := Finite (-2).
Definition m3 : LogVal := Finite 3.
Definition m4 : LogVal := Finite (-1).

Compute kadane_log [m1; m2; m3; m4].

(*
=================================================================================
CORRECTNESS
=================================================================================
*)

(* The main correctness theorem from KadanesAlgorithm.v applies directly *)
Check @Generalized_Kadane_Correctness LogVal LogVal_Semiring.

(*
Theorem: For any list of log-space values,
  gform8 vals = gform1 vals

This means the efficient implementation correctly computes the maximum
log-sum-exp (approximated as max-plus) over all contiguous subsequences.
*)

(*
=================================================================================
INTERPRETATION AND APPLICATIONS
=================================================================================

What does this mean practically?

1. **Probability Theory:**
   Working with log-probabilities avoids numerical underflow. Kadane's
   algorithm finds the contiguous subsequence with maximum sum in log-space,
   which corresponds to maximum product in probability space.

   Applications:
   - Hidden Markov Models (finding most likely state sequence)
   - Sequence alignment (finding best matching subsequence)
   - Signal processing (finding maximum likelihood segment)

2. **Information Theory:**
   Log values represent information content. The algorithm finds the
   subsequence that maximizes total information.

3. **Machine Learning:**
   Log-semirings are used in:
   - Forward-backward algorithm for HMMs
   - Viterbi algorithm (when using max approximation)
   - Probabilistic graphical models
   - Neural network training (log-likelihood maximization)

4. **Tropical Semiring Connection:**
   Our approximation log(e^x + e^y) ≈ max(x,y) is exactly the tropical
   semiring (max, +), also known as the min-plus algebra when negated.
   This is widely used in:
   - Shortest path problems
   - Scheduling algorithms
   - Optimization theory

The key insight: Kadane's algorithm works on ANY semiring, including
this numerically stable log-space representation!
*)

(*
=================================================================================
COMPARISON WITH OTHER SEMIRINGS
=================================================================================

| Semiring           | Addition (⊕)      | Multiplication (⊗) | Kadane finds      |
|--------------------|-------------------|--------------------|-------------------|
| Tropical (max,+)   | max(x,y)          | x + y              | Max subarray sum  |
| Natural (ℕ,+,×)    | x + y             | x × y              | Max product       |
| Log (this file)    | max(x,y)          | x + y              | Max log-prob sum  |
| Endomorphism       | (a+b)x            | (ab)x              | Endo composition  |

All use the SAME algorithmic framework from KadanesAlgorithm.v!

Note: This log-semiring is isomorphic to the tropical semiring.
The difference is interpretation:
- Tropical: Direct max-plus optimization
- Log: Approximation of log-sum-exp for probability computations
*)
