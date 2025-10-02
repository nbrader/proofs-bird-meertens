Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import FreeMonoid.StructSemiring.
Require Import CoqUtilLib.ListFunctions.
Require Import KadanesAlgorithm.KadanesAlgorithm.

(*
=================================================================================
EXPLORATION: Can we define gform8 for general semirings?
=================================================================================

GOAL: Prove the fold-scan fusion law:
  fold_right op_1 identity_a (scan_right op_2 identity_b xs) =
  fst (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs)

where:
  op_3 x (u, v) := let w := op_2 x v in (op_1 u w, w)

KEY INSIGHT: Use (op_1 identity_b identity_a, identity_b) as the initial accumulator
instead of (identity_a, identity_b). This makes the base case trivial!

DISCOVERY PROCESS:
1. Tried original form with (identity_a, identity_b) → base case failed
2. Identified that we need op_1 to be COMMUTATIVE (for inductive step)
3. Initially thought we needed identity_b to be a right identity for op_1
4. USER CORRECTION: Changed RHS to use (op_1 identity_b identity_a, identity_b)
5. BREAKTHROUGH: The proof works with ONLY commutativity required!

PYTHON TESTING CONFIRMED:
- ✓ Commutativity IS required (fusion fails without it)
- ✗ Right identity is NOT required (fusion holds even when violated)

FINAL RESULT: Only ONE assumption needed!
  - op_1 must be COMMUTATIVE
  - No identity requirements!

For semirings:
  ✓ add_op is commutative (add_comm) - SUFFICIENT!
*)

(* Auxiliary lemma: snd of fold with op_3 tracks fold with op_2 *)
Lemma fold_pair_snd_tracks_fold :
  forall {A B : Type}
    (op_1 : B -> B -> B)
    (op_2 : A -> B -> B)
    (identity_a : B)
    (identity_b : B)
    (xs : list A),
  let op_3 := fun x (uv : B * B) =>
    let (u, v) := uv in
    let w := op_2 x v in
    (op_1 u w, w)
  in
  snd (fold_right op_3 (identity_a, identity_b) xs) = fold_right op_2 identity_b xs.
Proof.
  intros A B op_1 op_2 identity_a identity_b xs op_3.
  induction xs as [|x xs' IH].
  - simpl. reflexivity.
  - simpl fold_right.
    unfold op_3 at 1.
    destruct (fold_right op_3 (identity_a, identity_b) xs') as [u v].
    simpl snd.
    simpl snd in IH.
    rewrite IH.
    reflexivity.
Qed.

(*
=================================================================================
THE FUSION LAW
=================================================================================
*)

(* Main version: ONLY commutativity required! *)
Lemma fold_scan_fusion :
  forall {A B : Type}
    (op_1 : B -> B -> B)
    (op_2 : A -> B -> B)
    (identity_a : B)
    (identity_b : B)
    (op_1_comm : forall x y, op_1 x y = op_1 y x)           (* REQUIRED: commutativity *)
    (xs : list A),
  let op_3 := fun x (uv : B * B) =>
    let (u, v) := uv in
    let w := op_2 x v in
    (op_1 u w, w)
  in
  fold_right op_1 identity_a (scan_right op_2 identity_b xs) =
  fst (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs).
Proof.
  intros A B op_1 op_2 identity_a identity_b op_1_comm xs op_3.
  induction xs as [|x xs' IH].
  - (* Base: scan_right gives [identity_b], fold gives op_1 identity_b identity_a *)
    simpl. reflexivity.
  - (* Inductive step *)
    simpl scan_right.
    simpl fold_right at 1.
    assert (Hsnd: fold_right op_2 identity_b xs' =
                  snd (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs')).
    { symmetry. apply fold_pair_snd_tracks_fold. }
    rewrite Hsnd.
    rewrite IH.
    (* Now both sides use fold_right op_3 (op_1 identity_b identity_a, identity_b) xs' *)
    remember (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs') as pair eqn:Hpair.
    destruct pair as [u v].
    simpl fst. simpl snd.
    rewrite <- Hpair.
    unfold op_3. simpl fst.
    apply op_1_comm.
Qed.

(*
=================================================================================
APPLICATION TO SEMIRINGS: DOES IT WORK?
=================================================================================

For semirings, we want:
  op_1 = add_op
  op_2 = horner_op = λx y. add_op (mul_op x y) mul_one
  identity_a = add_zero
  identity_b = mul_one

Requirement 1: add_op commutative? ✓ YES (add_comm)
Requirement 2: add_op x mul_one = x? ✗ NO in general!

The issue: mul_one (𝟏) is NOT an identity for add_op (⊕).
For example, in the tropical semiring: 𝟎 ⊕ 𝟏 = max(-∞, 0) = 0 ≠ -∞ = 𝟎

RESOLUTION: We might need a different pair of identities, OR the fusion law
works in a modified form for specific semirings.
*)

(* Placeholder definition of gform8 - may not equal gform7 for all semirings *)
Definition gform8 {A : Type} `{Semiring A} : list A -> A :=
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  let pair_step := fun x (uv : A * A) =>
    let (u, v) := uv in
    let w := horner_op x v in
    (add_op u w, w)
  in
  fun xs => fst (fold_right pair_step (add_zero, mul_one) xs).
