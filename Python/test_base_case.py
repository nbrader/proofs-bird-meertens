#!/usr/bin/env python3
"""
Investigate the base case of the fusion law more carefully.
"""

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
    from functools import reduce
    return reduce(lambda acc, x: op(x, acc), reversed(xs), identity)

# Base case: xs = []
print("BASE CASE: xs = []")
print("=" * 60)

# Example with max and plus
op_1 = lambda x, y: max(x, y)
op_2 = lambda x, y: x + y
identity_a = 0  # or -inf
identity_b = 0

xs = []

# LHS: fold_right op_1 identity_a (scan_right op_2 identity_b [])
scan_result = scan_right(op_2, identity_b, xs)
print(f"scan_right op_2 {identity_b} [] = {scan_result}")

lhs = fold_right(op_1, identity_a, scan_result)
print(f"fold_right op_1 {identity_a} {scan_result} = {lhs}")

# RHS: fst (fold_right op_3 (identity_a, identity_b) [])
def op_3(x, uv):
    u, v = uv
    w = op_2(x, v)
    return (op_1(u, w), w)

pair_result = fold_right(op_3, (identity_a, identity_b), xs)
print(f"fold_right op_3 ({identity_a}, {identity_b}) [] = {pair_result}")

rhs = pair_result[0]
print(f"fst = {rhs}")

print(f"\nLHS = {lhs}, RHS = {rhs}, Equal? {lhs == rhs}")

print("\n" + "=" * 60)
print("ANALYSIS:")
print("=" * 60)
print(f"scan_right op_2 identity_b [] = [identity_b] = [{identity_b}]")
print(f"fold_right op_1 identity_a [identity_b]")
print(f"  = op_1 identity_b identity_a")
print(f"  = op_1 {identity_b} {identity_a}")
print(f"  = {op_1(identity_b, identity_a)}")

print(f"\nfst (fold_right op_3 (identity_a, identity_b) [])")
print(f"  = fst (identity_a, identity_b)")
print(f"  = {identity_a}")

print(f"\nFor equality: op_1 identity_b identity_a = identity_a")
print(f"  op_1 {identity_b} {identity_a} = {op_1(identity_b, identity_a)}")
print(f"  identity_a = {identity_a}")
print(f"  Equal? {op_1(identity_b, identity_a) == identity_a}")

print("\n" + "=" * 60)
print("DIFFERENT IDENTITY_A VALUES:")
print("=" * 60)

for id_a in [0, -100, float('-inf')]:
    result = op_1(identity_b, id_a)
    print(f"  identity_a = {id_a}: op_1({identity_b}, {id_a}) = {result}, equal? {result == id_a}")

print("\n" + "=" * 60)
print("CONCLUSION:")
print("=" * 60)
print("When identity_a = -inf and identity_b = 0:")
print(f"  max(0, -inf) = {max(0, float('-inf'))}")
print(f"  This equals -inf? {max(0, float('-inf')) == float('-inf')}")
print("\nSo the base case FAILS when identity_a = -inf and identity_b = 0!")
print("But it WORKS when identity_a = 0 and identity_b = 0!")
