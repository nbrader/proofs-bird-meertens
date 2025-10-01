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
*)

(* We'll show that tropical semiring violates kadane_horner_property *)

(*
  Counterexample to kadane_horner_property:

  Let xs = [Finite 2, Finite 3]

  LHS: semiring_product xs = fold_right tropical_mul (Finite 0) [Finite 2, Finite 3]
       = tropical_mul (Finite 2) (tropical_mul (Finite 3) (Finite 0))
       = tropical_mul (Finite 2) (Finite (3 + 0))
       = tropical_mul (Finite 2) (Finite 3)
       = Finite (2 + 3)
       = Finite 5

  RHS: semiring_sum (map semiring_product (inits xs))

  inits xs = [[], [Finite 2], [Finite 2, Finite 3]]

  semiring_product [] = Finite 0
  semiring_product [Finite 2] = tropical_mul (Finite 2) (Finite 0) = Finite 2
  semiring_product [Finite 2, Finite 3] = Finite 5

  semiring_sum [Finite 0, Finite 2, Finite 5]
    = fold_right tropical_add NegInf [Finite 0, Finite 2, Finite 5]
    = tropical_add (Finite 0) (tropical_add (Finite 2) (tropical_add (Finite 5) NegInf))
    = tropical_add (Finite 0) (tropical_add (Finite 2) (Finite 5))
    = tropical_add (Finite 0) (Finite (max 2 5))
    = tropical_add (Finite 0) (Finite 5)
    = Finite (max 0 5)
    = Finite 5

  So in this case LHS = RHS! Let me try another example...
*)

(*
  Actually, let me reconsider. The kadane_horner_property states:

  semiring_product xs = semiring_sum (map semiring_product (inits xs))

  For tropical semiring:
  - semiring_product computes the sum of all elements
  - semiring_sum computes the maximum
  - The RHS computes the maximum over all prefix sums

  So the property says: sum of all elements = max over all prefix sums

  Counterexample: xs = [Finite (-1), Finite 2]

  LHS: semiring_product xs = Finite ((-1) + 2) = Finite 1

  RHS: inits xs = [[], [Finite (-1)], [Finite (-1), Finite 2]]
       products: [Finite 0, Finite (-1), Finite 1]
       max: Finite (max 0 (max (-1) 1)) = Finite 1

  Still equal! Let me think more carefully...
*)

(*
  Wait, I need to check mul_one_add_absorb:

  mul_one_add_absorb: add_op mul_one add_zero = add_zero

  For tropical semiring:
  - mul_one = Finite 0
  - add_zero = NegInf
  - add_op = tropical_add (max)

  So: tropical_add (Finite 0) NegInf = Finite 0 ≠ NegInf

  This is the violation!
*)

Lemma tropical_violates_mul_one_add_absorb :
  @add_op ExtZ ExtZ_TropicalSemiring
         (@mul_one ExtZ ExtZ_TropicalSemiring)
         (@add_zero ExtZ ExtZ_TropicalSemiring)
  <> @add_zero ExtZ ExtZ_TropicalSemiring.
Proof.
  simpl.
  (* add_op mul_one add_zero = tropical_add (Finite 0) NegInf *)
  unfold tropical_add.
  (* This simplifies to Finite 0 *)
  (* We need to show Finite 0 <> NegInf *)
  discriminate.
Qed.

(*
  This proves that the tropical semiring cannot be a KadaneSemiring
  because it violates the mul_one_add_absorb property.

  Intuitively, this makes sense:
  - In KadaneSemiring, we need mul_one to act as an "absorbing element"
    when added to add_zero
  - In the tropical semiring, Finite 0 is the multiplicative identity,
    but when we "add" it (take max with) NegInf, we get Finite 0, not NegInf
  - This breaks the structure needed for Kadane's algorithm
*)

Theorem tropical_not_kadane :
  ~ @KadaneSemiring ExtZ ExtZ_TropicalSemiring.
Proof.
  intro H_kadane.
  destruct H_kadane as [_ H_absorb _].
  (* H_absorb states that add_op mul_one add_zero = add_zero *)
  (* But we've proven this is false *)
  apply tropical_violates_mul_one_add_absorb.
  exact H_absorb.
Qed.

(*
  CONCLUSION:

  The tropical semiring (max-plus semiring) is a proper semiring that
  satisfies all standard semiring axioms, but it does NOT satisfy the
  additional KadaneSemiring properties.

  Specifically, it violates mul_one_add_absorb, which requires that
  the multiplicative identity acts as an absorbing element when added
  to the additive identity.

  This demonstrates that KadaneSemiring is a genuinely restrictive
  subclass of semirings, and Kadane's algorithm framework only applies
  to semirings with this special property.

  The practical implication: while the tropical semiring naturally
  expresses maximum-subarray-like computations, it doesn't fit the
  exact algebraic structure that makes the full Kadane derivation
  (form1 → form8) work without additional conditions.
*)
