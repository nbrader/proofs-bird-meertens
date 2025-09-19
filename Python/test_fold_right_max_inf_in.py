#!/usr/bin/env python3
"""
Test script for fold_right_max_inf_in lemma.

This script tests the property that for a non-empty list xs,
fold_right_max_inf(xs) always returns an element that is in xs.

Lemma: forall (xs : list Z), xs <> [] -> Z_plus_neg_inf_In (fold_right_max_inf xs) xs.

Translation to Python:
- Z_plus_neg_inf is either a Z value or NegInf
- fold_right_max_inf(xs) = fold_right(max_op, NegInf, map(Z_val, xs))
- Z_plus_neg_inf_In(x, xs) = True iff x is Z_val(z) and z in xs
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

def z_plus_neg_inf_in(x: Z_plus_neg_inf, xs: List[int]) -> bool:
    """Check if x is in xs according to Z_plus_neg_inf_In definition"""
    if isinstance(x, NegInf):
        return False
    # x is an integer
    return x in xs

def test_fold_right_max_inf_in():
    """Test the fold_right_max_inf_in lemma"""

    test_cases = [
        [1],
        [1, 2],
        [2, 1],
        [1, 2, 3],
        [3, 2, 1],
        [1, 3, 2],
        [-1, -2, -3],
        [-3, -1, -2],
        [0],
        [0, 1, -1],
        [100, -50, 25],
        [5, 5, 5],  # duplicates
        [-10, -5, -1, 0, 1, 5, 10],  # mixed
    ]

    # Add some random test cases
    for _ in range(50):
        size = random.randint(1, 10)
        xs = [random.randint(-100, 100) for _ in range(size)]
        test_cases.append(xs)

    failures = 0
    total = 0

    for xs in test_cases:
        if not xs:  # Skip empty lists
            continue

        result = fold_right_max_inf(xs)
        is_in = z_plus_neg_inf_in(result, xs)

        total += 1
        if not is_in:
            failures += 1
            print(f"FAIL: xs = {xs}")
            print(f"  fold_right_max_inf(xs) = {result}")
            print(f"  z_plus_neg_inf_in(result, xs) = {is_in}")
            print()
        else:
            print(f"PASS: xs = {xs}, result = {result}")

    print(f"\nResults: {total - failures}/{total} tests passed")

    if failures == 0:
        print("✅ All tests passed! The lemma appears to be TRUE.")
    else:
        print(f"❌ {failures} tests failed! The lemma might be FALSE or implementation incorrect.")

    return failures == 0

def test_fold_right_max_inf_returns_max():
    """Additional test: verify fold_right_max_inf returns the maximum element"""

    print("\nAdditional test: Does fold_right_max_inf return the maximum?")

    test_cases = [
        [1],
        [1, 2],
        [2, 1],
        [1, 2, 3],
        [3, 2, 1],
        [-1, -2, -3],
        [0, 1, -1],
        [100, -50, 25],
    ]

    for xs in test_cases:
        result = fold_right_max_inf(xs)
        expected_max = max(xs)

        if isinstance(result, NegInf):
            print(f"UNEXPECTED: xs = {xs}, got NegInf instead of max")
        elif result == expected_max:
            print(f"PASS: xs = {xs}, max = {result}")
        else:
            print(f"FAIL: xs = {xs}, expected max = {expected_max}, got = {result}")

if __name__ == "__main__":
    print("Testing fold_right_max_inf_in lemma")
    print("=" * 50)

    success = test_fold_right_max_inf_in()
    test_fold_right_max_inf_returns_max()

    print("\nConclusion:")
    if success:
        print("The fold_right_max_inf_in lemma is computationally verified as TRUE.")
        print("This supports proceeding with the Coq proof.")
    else:
        print("The lemma appears to be FALSE or there's an implementation error.")
        print("Review the definitions before attempting the Coq proof.")