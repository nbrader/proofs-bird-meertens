#!/usr/bin/env python3
"""
Test which assumptions are actually required for the fold-scan fusion law.

Current assumptions:
1. op_1 is commutative
2. identity_b is a right identity for op_1 (op_1 x identity_b = x)

We'll test counterexamples to see if we can violate the law by breaking each assumption.
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

def test_fusion(op_1, op_2, identity_a, identity_b, xs, name):
    """Test if fusion law holds."""
    def op_3(x, uv):
        u, v = uv
        w = op_2(x, v)
        return (op_1(u, w), w)

    # LHS
    scan_result = scan_right(op_2, identity_b, xs)
    lhs = fold_right(op_1, identity_a, scan_result)

    # RHS with corrected initial accumulator
    initial = (op_1(identity_b, identity_a), identity_b)
    pair_result = fold_right(op_3, initial, xs)
    rhs = pair_result[0]

    print(f"\n{name}:")
    print(f"  xs = {xs}")
    print(f"  LHS = {lhs}")
    print(f"  RHS = {rhs}")
    print(f"  Equal? {lhs == rhs}")
    return lhs == rhs

print("=" * 80)
print("TEST 1: Non-commutative op_1 (subtraction)")
print("=" * 80)
# op_1 = subtraction (NOT commutative)
# op_2 = addition
# identity_b = 0 is right identity for subtraction: x - 0 = x ✓
result1 = test_fusion(
    op_1=lambda x, y: x - y,
    op_2=lambda x, y: x + y,
    identity_a=0,
    identity_b=0,
    xs=[1, 2, 3],
    name="Subtraction (non-commutative) with addition"
)
print(f"\nCommutative? No")
print(f"Right identity? Yes (x - 0 = x)")
print(f"Fusion holds? {result1}")

print("\n" + "=" * 80)
print("TEST 2: identity_b NOT a right identity for op_1")
print("=" * 80)
# op_1 = max (commutative)
# op_2 = addition
# identity_b = 5, but max(x, 5) != x for x < 5
result2 = test_fusion(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: x + y,
    identity_a=0,
    identity_b=5,  # NOT a right identity for max
    xs=[1, 2, 3],
    name="Max with identity_b=5 (not right identity)"
)
print(f"\nCommutative? Yes")
print(f"Right identity? No (max(0, 5) = 5 ≠ 0)")
print(f"Fusion holds? {result2}")

# Test with values where it's more obvious
print("\n" + "=" * 80)
print("TEST 3: identity_b NOT right identity - clearer example")
print("=" * 80)
result3 = test_fusion(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: x + y,
    identity_a=-100,
    identity_b=10,
    xs=[1, 2],
    name="Max with identity_b=10, identity_a=-100"
)
print(f"\nRight identity check: max(-100, 10) = {max(-100, 10)} (should be -100 if right identity)")
print(f"Fusion holds? {result3}")

print("\n" + "=" * 80)
print("TEST 4: Both assumptions violated")
print("=" * 80)
# Non-commutative AND wrong identity
result4 = test_fusion(
    op_1=lambda x, y: x - y,  # non-commutative
    op_2=lambda x, y: x + y,
    identity_a=0,
    identity_b=5,  # NOT right identity: x - 5 ≠ x
    xs=[1, 2, 3],
    name="Subtraction with identity_b=5"
)
print(f"\nCommutative? No")
print(f"Right identity? No (x - 5 ≠ x)")
print(f"Fusion holds? {result4}")

print("\n" + "=" * 80)
print("TEST 5: Both assumptions satisfied (control)")
print("=" * 80)
result5 = test_fusion(
    op_1=lambda x, y: max(x, y),  # commutative
    op_2=lambda x, y: x + y,
    identity_a=float('-inf'),
    identity_b=0,  # right identity: max(x, 0) = x for x >= 0
    xs=[1, 2, 3],
    name="Max with proper identity_b=0"
)
print(f"\nCommutative? Yes")
print(f"Right identity? Yes (max(x, 0) = x for x >= 0)")
print(f"Fusion holds? {result5}")

print("\n" + "=" * 80)
print("SUMMARY")
print("=" * 80)
print(f"Non-commutative op_1: {result1}")
print(f"Wrong right identity: {result2}")
print(f"Wrong right identity (clearer): {result3}")
print(f"Both violated: {result4}")
print(f"Both satisfied (control): {result5}")

print("\n" + "=" * 80)
print("CONCLUSION")
print("=" * 80)
print("If ANY test with violated assumptions returns True, that assumption is not required.")
print("If ALL tests with violated assumptions return False, all assumptions are required.")
