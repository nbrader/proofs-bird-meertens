#!/usr/bin/env python3
"""
Test the fusion law when identity_a = identity_b.
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

def test_fusion(op_1, op_2, identity, xs, name):
    def op_3(x, uv):
        u, v = uv
        w = op_2(x, v)
        return (op_1(u, w), w)

    scan_result = scan_right(op_2, identity, xs)
    lhs = fold_right(op_1, identity, scan_result)
    pair_result = fold_right(op_3, (identity, identity), xs)
    rhs = pair_result[0]

    print(f"\n{name}:")
    print(f"  xs = {xs}, identity = {identity}")
    print(f"  LHS = {lhs}, RHS = {rhs}, Equal? {lhs == rhs}")
    return lhs == rhs

print("=" * 80)
print("HYPOTHESIS: Fusion law works when identity_a = identity_b")
print("=" * 80)

# Test 1: Max and plus with identity = 0
test_fusion(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: x + y,
    identity=0,
    xs=[1, 2, 3],
    name="Max/plus, identity=0"
)

# Test 2: Max and plus with identity = -inf
test_fusion(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: x + y,
    identity=float('-inf'),
    xs=[1, 2, 3],
    name="Max/plus, identity=-inf"
)

# Test 3: Max and horner with identity = 0
test_fusion(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: max(x + y, 0),
    identity=0,
    xs=[1, -2, 3],
    name="Max/nonNegPlus, identity=0"
)

# Test 4: Max and horner with identity = 1
test_fusion(
    op_1=lambda x, y: max(x, y),
    op_2=lambda x, y: max(x + y, 1),
    identity=1,
    xs=[1, 2, 3],
    name="Max/horner_1, identity=1"
)

print("\n" + "=" * 80)
print("KEY INSIGHT:")
print("=" * 80)
print("When identity_a = identity_b = e:")
print("  Base case: op_1 e e = e (need op_1 to have e as identity)")
print("  So we need: e is an identity for BOTH op_1 AND for the result of op_2!")
print("\nFor semirings:")
print("  op_1 = add_op, op_2 = horner_op")
print("  horner_op x y = add_op (mul_op x y) mul_one")
print("  If we use identity = add_zero:")
print("    - add_op add_zero add_zero = add_zero ✓")
print("    - horner_op x add_zero = add_op (mul_op x add_zero) mul_one")
print("                            = add_op add_zero mul_one")
print("                            = mul_one")
print("  So horner_op doesn't preserve add_zero!")
