#!/usr/bin/env python3
"""
Test the fold-scan fusion law with concrete examples.

The law states:
  fold_right op_1 identity_a (scan_right op_2 identity_b xs) =
  fst (fold_right op_3 (identity_a, identity_b) xs)

where:
  op_3 x (u, v) = (op_1 u (op_2 x v), op_2 x v)

Requirements discovered:
1. op_1 must be commutative
2. identity_b must be a right identity for op_1 (op_1 x identity_b = x)
"""

from functools import reduce
from typing import List, Tuple, Callable, Any

def scan_right(op, identity, xs):
    """
    scan_right op identity [x1, x2, x3]
    = [op x1 (op x2 (op x3 identity)), op x2 (op x3 identity), op x3 identity, identity]
    """
    if not xs:
        return [identity]

    result = [identity]
    acc = identity
    for x in reversed(xs):
        acc = op(x, acc)
        result.insert(0, acc)
    return result

def fold_right(op, identity, xs):
    """fold_right op identity xs"""
    if not xs:
        return identity
    return reduce(lambda acc, x: op(x, acc), reversed(xs), identity)

def test_fusion_law(op_1, op_2, identity_a, identity_b, xs, name="Test"):
    """
    Test if the fusion law holds for given operations and data.
    """
    # Define op_3
    def op_3(x, uv):
        u, v = uv
        w = op_2(x, v)
        return (op_1(u, w), w)

    # LHS: fold_right op_1 identity_a (scan_right op_2 identity_b xs)
    scan_result = scan_right(op_2, identity_b, xs)
    lhs = fold_right(op_1, identity_a, scan_result)

    # RHS: fst (fold_right op_3 (identity_a, identity_b) xs)
    pair_result = fold_right(op_3, (identity_a, identity_b), xs)
    rhs = pair_result[0]

    print(f"\n{name}:")
    print(f"  xs = {xs}")
    print(f"  scan_right op_2 {identity_b} xs = {scan_result}")
    print(f"  LHS (fold scan) = {lhs}")
    print(f"  RHS (fst fold pair) = {rhs}")
    print(f"  Equal? {lhs == rhs}")

    # Check requirements
    print(f"\n  Checking requirements:")

    # Check commutativity of op_1
    test_vals = [identity_a, identity_b, 0, 1, 2, -1]
    comm_holds = all(op_1(x, y) == op_1(y, x) for x in test_vals for y in test_vals)
    print(f"    op_1 commutative? {comm_holds}")

    # Check identity_b is right identity for op_1
    id_holds = all(op_1(x, identity_b) == x for x in test_vals)
    print(f"    op_1 x identity_b = x? {id_holds}")

    return lhs == rhs

# Example 1: Integer addition for both ops (should work)
print("=" * 80)
print("EXAMPLE 1: op_1 = +, op_2 = +, identity_a = 0, identity_b = 0")
print("=" * 80)
result1 = test_fusion_law(
    op_1=lambda x, y: x + y,
    op_2=lambda x, y: x + y,
    identity_a=0,
    identity_b=0,
    xs=[1, 2, 3],
    name="Integer addition"
)

# Example 2: Max and plus (tropical-like, identity_b = 0)
print("\n" + "=" * 80)
print("EXAMPLE 2: op_1 = max, op_2 = +, identity_a = 0, identity_b = 0")
print("=" * 80)
result2 = test_fusion_law(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: x + y,
    identity_a=0,
    identity_b=0,
    xs=[1, 2, 3],
    name="Max and plus with identity_b = 0"
)

# Example 3: Max and plus (tropical-like, identity_a = -inf, identity_b = 0)
print("\n" + "=" * 80)
print("EXAMPLE 3: op_1 = max, op_2 = +, identity_a = -inf, identity_b = 0")
print("=" * 80)
result3 = test_fusion_law(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: x + y,
    identity_a=float('-inf'),
    identity_b=0,
    xs=[1, 2, 3],
    name="Max and plus with correct identities"
)

# Example 4: Testing with negative numbers
print("\n" + "=" * 80)
print("EXAMPLE 4: op_1 = max, op_2 = +, with negative numbers")
print("=" * 80)
result4 = test_fusion_law(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: x + y,
    identity_a=float('-inf'),
    identity_b=0,
    xs=[-2, 1, -3, 4],
    name="Max and plus with negative numbers"
)

# Example 5: Semiring case - op_2 = horner_op = λx y. max((x + y), 1)
print("\n" + "=" * 80)
print("EXAMPLE 5: op_1 = max, op_2 = horner_op (max(x+y, 1)), identity_a = 0, identity_b = 1")
print("=" * 80)
result5 = test_fusion_law(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: max(x + y, 1),
    identity_a=0,
    identity_b=1,
    xs=[1, 2, 3],
    name="Horner op case"
)

# Example 6: Check if identity_b = 1 is right identity for max
print("\n" + "=" * 80)
print("EXAMPLE 6: Checking if 1 is right identity for max")
print("=" * 80)
test_vals = [0, 1, 2, 3, -1, -5]
print("Testing max(x, 1) == x:")
for x in test_vals:
    result = max(x, 1)
    print(f"  max({x}, 1) = {result}, equals {x}? {result == x}")

# Example 7: What if we use identity_a = identity_b = 0 for max/plus?
print("\n" + "=" * 80)
print("EXAMPLE 7: op_1 = max, op_2 = max(x+y, 0) [nonNegPlus], identity_a = identity_b = 0")
print("=" * 80)
result7 = test_fusion_law(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: max(x + y, 0),
    identity_a=0,
    identity_b=0,
    xs=[1, -2, 3],
    name="NonNegPlus with identity_b = 0"
)

print("\n" + "=" * 80)
print("SUMMARY")
print("=" * 80)
print(f"Example 1 (add/add): {result1}")
print(f"Example 2 (max/plus, both 0): {result2}")
print(f"Example 3 (max/plus, -inf/0): {result3}")
print(f"Example 4 (max/plus with negatives): {result4}")
print(f"Example 5 (max/horner with 0/1): {result5}")
print(f"Example 7 (max/nonNegPlus with 0/0): {result7}")
