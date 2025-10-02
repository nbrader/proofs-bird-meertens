#!/usr/bin/env python3
"""
Test if we can generalize the type signature of the fold-scan fusion law.

Current: op_1 : B -> B -> B, op_2 : A -> B -> B
Question: Can we have more general types?

Possible generalizations:
1. op_1 : C -> D -> E, op_2 : A -> B -> C, but need constraints
2. Different return types for op_1 and op_2
"""

from functools import reduce

def scan_right(op, identity, xs):
    if not xs:
        return [identity]
    result = [identity]
    acc = identity
    for x in reversed(xs):
        acc = op(x, acc)
        result.insert(0, acc)
    return result

def fold_right(op, identity, xs):
    if not xs:
        return identity
    return reduce(lambda acc, x: op(x, acc), reversed(xs), identity)

print("=" * 80)
print("ANALYZING TYPE CONSTRAINTS")
print("=" * 80)

print("""
Current fusion law:
  fold_right op_1 identity_a (scan_right op_2 identity_b xs) =
  fst (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs)

where op_3 x (u, v) = (op_1 u (op_2 x v), op_2 x v)

Type analysis:
  xs : list A
  op_2 : A -> B -> B    (takes A element and B accumulator, returns B)
  identity_b : B
  scan_right op_2 identity_b xs : list B

  op_1 : B -> B -> B    (takes two B values, returns B)
  identity_a : B
  fold_right op_1 identity_a : list B -> B

  LHS : B

For op_3:
  x : A
  (u, v) : (B, B)
  op_2 x v : B
  op_1 u (op_2 x v) : B  <- requires op_1 : B -> B -> B

So we MUST have op_1 : B -> B -> B for the types to work out!

The pair (u, v) has type (B, B), and we need:
  - v : B to pass to op_2 x v
  - u : B to pass to op_1 u ...
  - op_1 u (op_2 x v) : B to be first component of next pair

This forces B -> B -> B for op_1.
""")

print("\n" + "=" * 80)
print("COULD WE HAVE DIFFERENT TYPES FOR THE PAIR?")
print("=" * 80)

print("""
Could we use pair : (C, B) instead of (B, B)?

op_3 x (u, v) where u : C, v : B
  = (op_1 u (op_2 x v), op_2 x v)

This would require:
  - op_1 : C -> B -> C  (takes C and B, returns C)
  - op_2 : A -> B -> B  (unchanged)

But then:
  LHS = fold_right op_1 identity_a (scan_right op_2 identity_b xs)
      : fold_right op_1 identity_a : list B -> ?

  op_1 would need to work as : B -> B -> B on the LHS
  but be           : C -> B -> C in op_3

This is a contradiction unless C = B!
""")

print("\n" + "=" * 80)
print("CONCLUSION")
print("=" * 80)

print("""
The type signature is ALREADY maximally general!

We have:
  - Input type A (for list elements)
  - Accumulator/output type B
  - op_2 : A -> B -> B (processes inputs into accumulator type)
  - op_1 : B -> B -> B (combines two accumulators, must be commutative)

We CANNOT generalize further because:
1. The LHS uses op_1 to fold over list B
2. The RHS uses op_1 in the pair construction
3. Both uses must have the same type signature
4. The pair must maintain type (B, B) to work with op_2

The only possible relaxation would be to remove the commutativity requirement,
but we've proven that's essential (counterexamples fail without it).
""")

print("\n" + "=" * 80)
print("ALTERNATIVE FORMULATION: Different accumulator type?")
print("=" * 80)

print("""
What if we tried:
  pair : (C, B)
  op_1_init : B -> B -> C    (to create initial first component)
  op_1_step : C -> B -> C    (to update first component)
  op_1_fold : B -> B -> B    (to fold the scan)

Then:
  LHS: fold_right op_1_fold identity_a (scan_right op_2 identity_b xs)
  RHS: fst (fold_right op_3 (op_1_init identity_b identity_a, identity_b) xs)

  where op_3 x (u, v) = (op_1_step u (op_2 x v), op_2 x v)

But now the LHS produces type B and RHS produces type C, so they can't be equal!

Unless C = B, which brings us back to the original formulation.
""")

print("\n" + "=" * 80)
print("FINAL ANSWER")
print("=" * 80)
print("""
The current type signature is OPTIMAL and MAXIMALLY GENERAL:
  - forall {A B : Type}
  - op_1 : B -> B -> B (commutative)
  - op_2 : A -> B -> B
  - identity_a, identity_b : B

No further type generalization is possible while maintaining the fusion law.
The commutativity of op_1 is the ONLY semantic requirement.
""")
