#!/usr/bin/env python3
"""
Test script for fold_right_max_inf_returns_max lemma.

This script tests the property that if m is both an upper bound for all elements
in xs and m is in xs, then fold_right_max_inf(xs) = Z_val(m).

Lemma: forall (xs : list Z) (m : Z),
  (forall y, In y xs -> Z_val y <=_inf Z_val m) ->
  In m xs ->
  fold_right_max_inf xs = Z_val m.

Translation to Python:
- Z_plus_neg_inf_le(Z_val a, Z_val b) = (a <= b)
- The lemma states: if m is the maximum element in xs, then fold_right_max_inf(xs) = m
"""

from typing import Union, List
import random

# Type definitions
class NegInf:
    def __repr__(self):
        return "NegInf"

    def __eq__(self, other):
        return isinstance(other, NegInf)

Z_plus_neg_inf = Union[int, NegInf]

def z_val(z: int) -> int:
    """Convert regular integer to Z_val - just identity in Python"""
    return z

def z_plus_neg_inf_le(x: Z_plus_neg_inf, y: Z_plus_neg_inf) -> bool:
    """<= operation for Z_plus_neg_inf"""
    if isinstance(x, NegInf):
        return True
    if isinstance(y, NegInf):
        return False
    # Both are integers
    return x <= y

def z_plus_neg_inf_max(x: Z_plus_neg_inf, y: Z_plus_neg_inf) -> Z_plus_neg_inf:
    """Max operation for Z_plus_neg_inf"""
    if isinstance(x, NegInf):
        return y
    if isinstance(y, NegInf):
        return x
    # Both are integers
    return max(x, y)

def fold_right_max_inf(xs: List[int]) -> Z_plus_neg_inf:
    """
    fold_right Z_plus_neg_inf_max NegInf (map Z_val xs)
    """
    if not xs:
        return NegInf()

    result = NegInf()
    for x in reversed(xs):  # fold_right processes from right to left
        result = z_plus_neg_inf_max(z_val(x), result)

    return result

def is_upper_bound(m: int, xs: List[int]) -> bool:
    """Check if m is an upper bound for all elements in xs"""
    return all(z_plus_neg_inf_le(z_val(y), z_val(m)) for y in xs)

def test_fold_right_max_inf_returns_max():
    """Test the fold_right_max_inf_returns_max lemma"""

    # Generate test cases where m is both an upper bound and in the list
    test_cases = []

    # Simple cases where m is the maximum
    test_cases.extend([
        ([1], 1),
        ([1, 2], 2),
        ([2, 1], 2),
        ([1, 2, 3], 3),
        ([3, 2, 1], 3),
        ([1, 3, 2], 3),
        ([-1, -2, -3], -1),
        ([-3, -1, -2], -1),
        ([0], 0),
        ([0, 1, -1], 1),
        ([100, -50, 25], 100),
        ([5, 5, 5], 5),  # duplicates
        ([-10, -5, -1, 0, 1, 5, 10], 10),
    ])

    # Generate some random test cases
    for _ in range(20):
        size = random.randint(1, 8)
        xs = [random.randint(-50, 50) for _ in range(size)]
        m = max(xs)  # m is definitely the maximum, so it's an upper bound and in the list
        test_cases.append((xs, m))

    # Test cases with duplicated maximum
    for _ in range(10):
        size = random.randint(2, 6)
        xs = [random.randint(-30, 30) for _ in range(size - 1)]
        m = max(xs) if xs else 0
        xs.append(m)  # Add m again to ensure it's in the list
        test_cases.append((xs, m))

    failures = 0
    total = 0

    for xs, m in test_cases:
        # Verify preconditions
        if not is_upper_bound(m, xs):
            print(f"SKIP: m={m} is not an upper bound for xs={xs}")
            continue

        if m not in xs:
            print(f"SKIP: m={m} is not in xs={xs}")
            continue

        result = fold_right_max_inf(xs)
        expected = z_val(m)

        total += 1
        if result != expected:
            failures += 1
            print(f"FAIL: xs = {xs}, m = {m}")
            print(f"  Expected: {expected}")
            print(f"  Got: {result}")
            print()
        else:
            print(f"PASS: xs = {xs}, m = {m}, result = {result}")

    print(f"\nResults: {total - failures}/{total} tests passed")

    if failures == 0:
        print("✅ All tests passed! The lemma appears to be TRUE.")
    else:
        print(f"❌ {failures} tests failed! The lemma might be FALSE or implementation incorrect.")

    return failures == 0

def test_counterexamples():
    """Test cases where the preconditions are NOT met to verify they fail appropriately"""

    print("\nTesting counterexamples (where preconditions are not met):")

    # Case 1: m is in xs but not an upper bound
    xs = [1, 5, 3]
    m = 1  # m is in xs but not the maximum
    result = fold_right_max_inf(xs)
    print(f"xs = {xs}, m = {m} (not upper bound)")
    print(f"fold_right_max_inf(xs) = {result}, Z_val(m) = {m}")
    print(f"Equal? {result == m} (should be False)")

    # Case 2: m is an upper bound but not in xs
    xs = [1, 2, 3]
    m = 5  # m is an upper bound but not in xs
    if is_upper_bound(m, xs) and m not in xs:
        result = fold_right_max_inf(xs)
        print(f"xs = {xs}, m = {m} (upper bound but not in xs)")
        print(f"fold_right_max_inf(xs) = {result}, Z_val(m) = {m}")
        print(f"Equal? {result == m} (should be False)")

if __name__ == "__main__":
    print("Testing fold_right_max_inf_returns_max lemma")
    print("=" * 50)

    success = test_fold_right_max_inf_returns_max()
    test_counterexamples()

    print("\nConclusion:")
    if success:
        print("The fold_right_max_inf_returns_max lemma is computationally verified as TRUE.")
        print("This supports proceeding with the Coq proof.")
    else:
        print("The lemma appears to be FALSE or there's an implementation error.")
        print("Review the definitions before attempting the Coq proof.")