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
  op_3 x (u, v) := let w := op_2 x v in (op_1 w u, w)

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

SECOND BREAKTHROUGH: Swapping arguments in op_3 eliminates commutativity requirement!
- By using op_3 x (u, v) = (op_1 w u, w) instead of (op_1 u w, w)
- The fusion law holds with NO assumptions on op_1 at all!
- This is the maximally general form.

For semirings:
  ✓ add_op is commutative (add_comm) - so both versions work
  ✓ Non-commutative version works for ALL semirings automatically!
*)

(*
=================================================================================
THE FUSION LAW (Maximally General Form)
=================================================================================

This is the most general possible formulation:
- Type A: input elements
- Type B: accumulator/output type
- op_1 : B -> B -> B (NO CONSTRAINTS!)
- op_2 : A -> B -> B (no constraints)

Type analysis proves no further generalization is possible:
- LHS uses op_1 : B -> B -> B to fold over list B
- RHS uses op_1 : B -> B -> B in pair construction
- Both uses must have the same type signature
- The pair (u, v) must have type (B, B) to work with op_2

Any attempt to use different types (e.g., pair : (C, B)) creates a type
mismatch between LHS and RHS.
*)

(* Helper lemma: snd of fold with op_3 tracks fold with op_2 *)
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
    (op_1 w u, w)
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

Lemma fold_scan_fusion :
  forall {A B : Type}
    (op_1 : B -> B -> B)
    (op_2 : A -> B -> B)
    (identity_a : B)
    (identity_b : B)
    (xs : list A),
  let op_3 := fun x (uv : B * B) =>
    let (u, v) := uv in
    let w := op_2 x v in
    (op_1 w u, w)
  in
  fold_right op_1 identity_a (scan_right op_2 identity_b xs) =
  fst (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs).
Proof.
  intros A B op_1 op_2 identity_a identity_b xs op_3.
  induction xs as [|x xs' IH].
  - (* Base case *)
    simpl. reflexivity.
  - (* Inductive step *)
    simpl scan_right.
    simpl fold_right at 1.
    assert (Hsnd: fold_right op_2 identity_b xs' =
                  snd (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs')).
    { symmetry. apply fold_pair_snd_tracks_fold. }
    rewrite Hsnd.
    rewrite IH.
    remember (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs') as pair eqn:Hpair.
    destruct pair as [u v].
    simpl fst. simpl snd.
    rewrite <- Hpair.
    unfold op_3. simpl fst.
    reflexivity.
Qed.

(*
=================================================================================
APPLICATION TO SEMIRINGS: IT WORKS!
=================================================================================

For semirings, we use:
  op_1 = add_op
  op_2 = horner_op = λx y. add_op (mul_op x y) mul_one
  identity_a = add_zero
  identity_b = mul_one

Requirements: NONE! The fusion law holds with no assumptions.

The initial accumulator (add_op mul_one add_zero, mul_one) handles the
identity mismatch automatically - we don't need mul_one to be an identity
for add_op!
*)

(* gform8 for general semirings *)
Definition gform8 {A : Type} `{Semiring A} : list A -> A :=
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  let pair_step := fun x (uv : A * A) =>
    let (u, v) := uv in
    let w := horner_op x v in
    (add_op w u, w)
  in
  fun xs => fst (fold_right pair_step (add_op mul_one add_zero, mul_one) xs).
