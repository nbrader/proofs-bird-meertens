#!/usr/bin/env python3
"""
Test if we can avoid the commutativity requirement by swapping arguments
in the statement of the fusion law.

Current law requires commutativity:
  fold_right op_1 identity_a (scan_right op_2 identity_b xs) =
  fst (fold_right op_3 (op_1 identity_b identity_a, identity_b) xs)

where op_3 x (u, v) = (op_1 u (op_2 x v), op_2 x v)

At the final step, we need: op_1 (op_2 x v) u = op_1 u (op_2 x v)
which requires commutativity.

Question: Can we swap arguments somewhere to avoid this?
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

def test_variant(name, lhs_fn, rhs_fn, op_1, op_2, identity_a, identity_b, xs):
    """Test a variant of the fusion law."""
    lhs = lhs_fn(op_1, op_2, identity_a, identity_b, xs)
    rhs = rhs_fn(op_1, op_2, identity_a, identity_b, xs)

    print(f"\n{name}:")
    print(f"  xs = {xs}")
    print(f"  LHS = {lhs}")
    print(f"  RHS = {rhs}")
    print(f"  Equal? {lhs == rhs}")
    return lhs == rhs

# Test with non-commutative operation
op_1_nc = lambda x, y: x - y  # subtraction (non-commutative)
op_2_add = lambda x, y: x + y

print("=" * 80)
print("VARIANT 1: Original formulation (requires commutativity)")
print("=" * 80)

def lhs_v1(op_1, op_2, id_a, id_b, xs):
    return fold_right(op_1, id_a, scan_right(op_2, id_b, xs))

def rhs_v1(op_1, op_2, id_a, id_b, xs):
    def op_3(x, uv):
        u, v = uv
        w = op_2(x, v)
        return (op_1(u, w), w)
    return fold_right(op_3, (op_1(id_b, id_a), id_b), xs)[0]

result1 = test_variant(
    "Original (needs commutativity)",
    lhs_v1, rhs_v1,
    op_1_nc, op_2_add, 0, 0, [1, 2, 3]
)

print("\n" + "=" * 80)
print("VARIANT 2: Swap arguments in op_3")
print("=" * 80)
print("Try: op_3 x (u, v) = (op_1 (op_2 x v) u, op_2 x v)")

def rhs_v2(op_1, op_2, id_a, id_b, xs):
    def op_3(x, uv):
        u, v = uv
        w = op_2(x, v)
        return (op_1(w, u), w)  # Swapped!
    return fold_right(op_3, (op_1(id_b, id_a), id_b), xs)[0]

result2 = test_variant(
    "Swap in op_3",
    lhs_v1, rhs_v2,
    op_1_nc, op_2_add, 0, 0, [1, 2, 3]
)

print("\n" + "=" * 80)
print("VARIANT 3: Swap arguments in LHS fold")
print("=" * 80)
print("Try: fold_right (λx y. op_1 y x) instead")

def lhs_v3(op_1, op_2, id_a, id_b, xs):
    op_1_swapped = lambda x, y: op_1(y, x)
    return fold_right(op_1_swapped, id_a, scan_right(op_2, id_b, xs))

result3 = test_variant(
    "Swap in LHS fold",
    lhs_v3, rhs_v1,
    op_1_nc, op_2_add, 0, 0, [1, 2, 3]
)

print("\n" + "=" * 80)
print("VARIANT 4: Change initial accumulator")
print("=" * 80)
print("Try: (op_1 identity_a identity_b, identity_b) instead")

def rhs_v4(op_1, op_2, id_a, id_b, xs):
    def op_3(x, uv):
        u, v = uv
        w = op_2(x, v)
        return (op_1(u, w), w)
    return fold_right(op_3, (op_1(id_a, id_b), id_b), xs)[0]  # Swapped order!

result4 = test_variant(
    "Swap initial accumulator",
    lhs_v1, rhs_v4,
    op_1_nc, op_2_add, 0, 0, [1, 2, 3]
)

print("\n" + "=" * 80)
print("VARIANT 5: Both swaps (v2 + v4)")
print("=" * 80)

def rhs_v5(op_1, op_2, id_a, id_b, xs):
    def op_3(x, uv):
        u, v = uv
        w = op_2(x, v)
        return (op_1(w, u), w)  # Swapped in op_3
    return fold_right(op_3, (op_1(id_a, id_b), id_b), xs)[0]  # Swapped initial

result5 = test_variant(
    "Both swaps",
    lhs_v1, rhs_v5,
    op_1_nc, op_2_add, 0, 0, [1, 2, 3]
)

print("\n" + "=" * 80)
print("VARIANT 6: All three swaps (v3 + v2 + v4)")
print("=" * 80)

result6 = test_variant(
    "All swaps",
    lhs_v3, rhs_v5,
    op_1_nc, op_2_add, 0, 0, [1, 2, 3]
)

print("\n" + "=" * 80)
print("SUMMARY")
print("=" * 80)
print(f"Original (needs commutativity): {result1}")
print(f"Swap in op_3: {result2}")
print(f"Swap in LHS fold: {result3}")
print(f"Swap initial accumulator: {result4}")
print(f"Both swaps (op_3 + initial): {result5}")
print(f"All swaps: {result6}")

if any([result2, result3, result4, result5, result6]):
    print("\n✓ SUCCESS! Found variant(s) that work without commutativity!")
else:
    print("\n✗ No variant works - commutativity is essential")

# Test with more examples
print("\n" + "=" * 80)
print("TESTING SUCCESSFUL VARIANTS WITH MORE EXAMPLES")
print("=" * 80)

test_cases = [
    ([1, 2], "Small list"),
    ([5], "Singleton"),
    ([], "Empty list"),
    ([1, 2, 3, 4], "Longer list"),
]

for variant_num, (result, lhs_fn, rhs_fn) in [
    (2, (result2, lhs_v1, rhs_v2)),
    (3, (result3, lhs_v3, rhs_v1)),
    (4, (result4, lhs_v1, rhs_v4)),
    (5, (result5, lhs_v1, rhs_v5)),
    (6, (result6, lhs_v3, rhs_v5)),
]:
    if result:
        print(f"\nVariant {variant_num}:")
        all_pass = True
        for xs, desc in test_cases:
            passed = test_variant(desc, lhs_fn, rhs_fn, op_1_nc, op_2_add, 0, 0, xs)
            all_pass = all_pass and passed
        print(f"  All tests passed: {all_pass}")
