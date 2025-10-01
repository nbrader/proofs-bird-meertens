(*
  Proof that the tropical semiring (max-plus semiring) does NOT satisfy
  the KadaneSemiring properties defined in KadanesAlgorithm.v

  The tropical semiring:
  - Addition: Z.max (denoted ⊕)
  - Multiplication: Z.add (denoted ⊗)
  - Additive identity: negative infinity (denoted 𝟘)
  - Multiplicative identity: 0 (denoted 𝟙)

  This proof shows that KadaneSemiring is a specialized structure that
  does NOT hold for all semirings, and in particular fails for the
  standard tropical semiring.
*)

Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import FreeMonoid.StructSemiring.
Require Import FreeMonoid.SemiringLemmas.
Require Import KadanesAlgorithm.KadanesAlgorithm.
Import ListNotations.

Open Scope Z_scope.

(*
  The tropical semiring from SemiringLemmas uses ExtZ with:
  - add_op = tropical_add (max)
  - mul_op = tropical_mul (plus)
  - add_zero = NegInf
  - mul_one = Finite 0

  The violation occurs with mul_one_add_absorb:
  tropical_add (Finite 0) NegInf = Finite 0 ≠ NegInf
*)

Lemma tropical_violates_mul_one_add_absorb :
  @add_op ExtZ ExtZ_TropicalSemiring
         (@mul_one ExtZ ExtZ_TropicalSemiring)
         (@add_zero ExtZ ExtZ_TropicalSemiring)
  <> @add_zero ExtZ ExtZ_TropicalSemiring.
Proof.
  simpl.
  unfold tropical_add.
  discriminate.
Qed.

Theorem tropical_not_kadane :
  ~ @KadaneSemiring ExtZ ExtZ_TropicalSemiring.
Proof.
  intro H_kadane.
  destruct H_kadane as [_ H_absorb _].
  apply tropical_violates_mul_one_add_absorb.
  exact H_absorb.
Qed.
