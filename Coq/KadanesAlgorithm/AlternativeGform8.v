(*
  Exploration: What if we use (mul_one, mul_one) instead of (add_zero, mul_one) in gform8?

  This would change the required property from:
    mul_one_add_absorb: add_op mul_one add_zero = add_zero
  to:
    add_zero_eq_mul_one: add_zero = mul_one

  Question: Is this more or less restrictive?
*)

Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import CoqUtilLib.ListFunctions.
Require Import FreeMonoid.StructSemiring.
Require Import FreeMonoid.SemiringLemmas.
Require Import KadanesAlgorithm.KadanesAlgorithm.
Import ListNotations.

(*
  Analysis:

  The property add_zero = mul_one is EXTREMELY restrictive:
  - For integers (ℤ, +, ×): 0 ≠ 1
  - For tropical semiring (max, +): -∞ ≠ 0
  - For boolean semiring (∨, ∧): false ≠ true
  - For natural numbers (ℕ, +, ×): 0 ≠ 1

  In fact, requiring add_zero = mul_one essentially means we have a "unital" structure
  where the additive and multiplicative identities coincide.

  This is MUCH MORE restrictive than mul_one_add_absorb!

  The only semirings where add_zero = mul_one are extremely degenerate:
  - The trivial semiring (single element)
  - Possibly some constructed examples with special definitions

  Conclusion: Using (add_zero, mul_one) with mul_one_add_absorb is LESS restrictive
  than using (mul_one, mul_one) with add_zero = mul_one.

  The current formulation is better!
*)

(*
  However, there's another possibility: What if we define a variant that computes
  something different?

  If we use (mul_one, mul_one), the base case gives:
    scan_right horner_op mul_one [] = []
    fold_right add_op add_zero [] = add_zero
  But:
    fst (mul_one, mul_one) = mul_one

  So we'd need add_zero = mul_one for the base case to match.

  This doesn't help - it's strictly worse than mul_one_add_absorb.
*)

Definition gform8_alternative {A : Type} `{Semiring A} : list A -> A :=
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  fst ∘ fold_right (fun x uv => let '(u, v) := uv in
                                let w := horner_op v x in
                                (add_op u w, w)) (mul_one, mul_one).

(*
  For gform7 = gform8_alternative, we'd need to prove:

  semiring_sum (scan_right horner_op mul_one xs) =
  fst (fold_right ... (mul_one, mul_one) xs)

  Base case (xs = []):
    LHS = semiring_sum [] = add_zero
    RHS = fst (mul_one, mul_one) = mul_one

  Requires: add_zero = mul_one

  This is essentially a "rig" or "unital semiring" where 0 = 1,
  which collapses the entire structure to be trivial.
*)

(*
  Wait! What about (mul_one, add_zero) instead?

  Let's analyze this case:
*)

Definition gform8_mul_one_add_zero {A : Type} `{Semiring A} : list A -> A :=
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  fst ∘ fold_right (fun x uv => let '(u, v) := uv in
                                let w := horner_op v x in
                                (add_op u w, w)) (mul_one, add_zero).

(*
  For gform7 = gform8_mul_one_add_zero, we'd need to prove:

  semiring_sum (scan_right horner_op mul_one xs) =
  fst (fold_right ... (mul_one, add_zero) xs)

  Base case (xs = []):
    LHS = semiring_sum (scan_right horner_op mul_one [])
        = semiring_sum []
        = fold_right add_op add_zero []
        = add_zero

    RHS = fst (mul_one, add_zero)
        = mul_one

  Requires: add_zero = mul_one  (same problem!)

  So (mul_one, add_zero) also requires add_zero = mul_one.
*)

(*
  Actually, let me reconsider the base case more carefully.

  For scan_right:
    scan_right f z [] = []

  So:
    semiring_sum (scan_right horner_op mul_one [])
    = semiring_sum []
    = fold_right add_op add_zero []
    = add_zero

  And:
    fst (fold_right ... (init_u, init_v) [])
    = fst (init_u, init_v)
    = init_u

  So we need: add_zero = init_u

  For (add_zero, mul_one): init_u = add_zero ✓ (works!)
  For (mul_one, mul_one): init_u = mul_one (requires add_zero = mul_one ✗)
  For (mul_one, add_zero): init_u = mul_one (requires add_zero = mul_one ✗)

  CONCLUSION: The first component MUST be add_zero for the base case to work!

  Now what about the second component? Could we use (add_zero, add_zero)?
*)

Definition gform8_add_zero_add_zero {A : Type} `{Semiring A} : list A -> A :=
  let horner_op := fun x y => add_op (mul_op x y) mul_one in
  fst ∘ fold_right (fun x uv => let '(u, v) := uv in
                                let w := horner_op v x in
                                (add_op u w, w)) (add_zero, add_zero).

(*
  The second component `v` in the fold tracks the "current suffix value"
  and is used to compute: horner_op v x

  The invariant maintained is:
    v = fold_right horner_op init_v remaining_suffix

  In the base case with init_v = add_zero:
    v = fold_right horner_op add_zero []
      = add_zero

  But we need this to match:
    fold_right horner_op mul_one []
    = mul_one

  Because scan_right horner_op mul_one is defined using mul_one as the identity!

  So the second component must be mul_one to match the scan_right definition.

  FINAL CONCLUSION:
  - First component must be add_zero (for base case: sum of empty list)
  - Second component must be mul_one (to match scan_right's identity)

  The formulation (add_zero, mul_one) is uniquely determined!

  The mul_one_add_absorb property is needed in the proof, not for choosing
  the initial values, but for showing the computation is correct.
*)
