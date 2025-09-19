#!/usr/bin/env python3
"""
Test script for subgoals of fold_right_max_inf_returns_max lemma.

This script tests intermediate steps needed for the formal proof:
1. If m is in xs and is an upper bound, then fold_right_max_inf(xs) >= m
2. If m is in xs and is an upper bound, then fold_right_max_inf(xs) <= m
3. Combined: fold_right_max_inf(xs) = m

This incremental approach helps validate the proof strategy before attempting Coq.
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
    """fold_right Z_plus_neg_inf_max NegInf (map Z_val xs)"""
    if not xs:
        return NegInf()

    result = NegInf()
    for x in reversed(xs):  # fold_right processes from right to left
        result = z_plus_neg_inf_max(z_val(x), result)

    return result

def is_upper_bound(m: int, xs: List[int]) -> bool:
    """Check if m is an upper bound for all elements in xs"""
    return all(z_plus_neg_inf_le(z_val(y), z_val(m)) for y in xs)

def test_subgoal_1_lower_bound():
    """
    Subgoal 1: If m ∈ xs and m is upper bound, then fold_right_max_inf(xs) >= m

    This should always be true because the max operation includes m as a candidate.
    """
    print("=== Subgoal 1: fold_right_max_inf(xs) >= m when m ∈ xs and m is upper bound ===")

    test_cases = [
        ([1], 1),
        ([1, 2], 2),
        ([2, 1], 2),
        ([1, 2, 3], 3),
        ([3, 2, 1], 3),
        ([-1, -2, -3], -1),
        ([5, 5, 5], 5),  # duplicates
        ([0, 1, -1], 1),
    ]

    # Add random test cases
    for _ in range(20):
        size = random.randint(1, 8)
        xs = [random.randint(-50, 50) for _ in range(size)]
        m = max(xs)  # m is definitely the maximum
        test_cases.append((xs, m))

    failures = 0
    total = 0

    for xs, m in test_cases:
        # Verify preconditions
        if not is_upper_bound(m, xs) or m not in xs:
            continue

        result = fold_right_max_inf(xs)
        total += 1

        # Check if result >= m
        if isinstance(result, NegInf):
            failures += 1
            print(f"FAIL: xs={xs}, m={m}, got NegInf but expected >= {m}")
        elif result < m:
            failures += 1
            print(f"FAIL: xs={xs}, m={m}, got {result} < {m}")
        else:
            print(f"PASS: xs={xs}, m={m}, result={result} >= {m}")

    print(f"Subgoal 1 Results: {total - failures}/{total} tests passed")
    return failures == 0

def test_subgoal_2_upper_bound():
    """
    Subgoal 2: If m ∈ xs and m is upper bound, then fold_right_max_inf(xs) <= m

    This should be true because m is the maximum element.
    """
    print("\n=== Subgoal 2: fold_right_max_inf(xs) <= m when m ∈ xs and m is upper bound ===")

    test_cases = [
        ([1], 1),
        ([1, 2], 2),
        ([2, 1], 2),
        ([1, 2, 3], 3),
        ([3, 2, 1], 3),
        ([-1, -2, -3], -1),
        ([5, 5, 5], 5),  # duplicates
        ([0, 1, -1], 1),
    ]

    # Add random test cases
    for _ in range(20):
        size = random.randint(1, 8)
        xs = [random.randint(-50, 50) for _ in range(size)]
        m = max(xs)  # m is definitely the maximum
        test_cases.append((xs, m))

    failures = 0
    total = 0

    for xs, m in test_cases:
        # Verify preconditions
        if not is_upper_bound(m, xs) or m not in xs:
            continue

        result = fold_right_max_inf(xs)
        total += 1

        # Check if result <= m
        if isinstance(result, NegInf):
            print(f"PASS: xs={xs}, m={m}, NegInf <= {m}")
        elif result > m:
            failures += 1
            print(f"FAIL: xs={xs}, m={m}, got {result} > {m}")
        else:
            print(f"PASS: xs={xs}, m={m}, result={result} <= {m}")

    print(f"Subgoal 2 Results: {total - failures}/{total} tests passed")
    return failures == 0

def test_subgoal_3_equality():
    """
    Subgoal 3: Combined test - if both subgoals hold, then fold_right_max_inf(xs) = m
    """
    print("\n=== Subgoal 3: fold_right_max_inf(xs) = m (combination of subgoals 1&2) ===")

    test_cases = [
        ([1], 1),
        ([1, 2], 2),
        ([2, 1], 2),
        ([1, 2, 3], 3),
        ([3, 2, 1], 3),
        ([-1, -2, -3], -1),
        ([5, 5, 5], 5),  # duplicates
        ([0, 1, -1], 1),
    ]

    # Add random test cases
    for _ in range(30):
        size = random.randint(1, 8)
        xs = [random.randint(-50, 50) for _ in range(size)]
        m = max(xs)  # m is definitely the maximum
        test_cases.append((xs, m))

    failures = 0
    total = 0

    for xs, m in test_cases:
        # Verify preconditions
        if not is_upper_bound(m, xs) or m not in xs:
            continue

        result = fold_right_max_inf(xs)
        total += 1

        # Check if result = m
        if isinstance(result, NegInf):
            failures += 1
            print(f"FAIL: xs={xs}, m={m}, got NegInf but expected {m}")
        elif result != m:
            failures += 1
            print(f"FAIL: xs={xs}, m={m}, got {result} != {m}")
        else:
            print(f"PASS: xs={xs}, m={m}, result={result} = {m}")

    print(f"Subgoal 3 Results: {total - failures}/{total} tests passed")
    return failures == 0

def test_key_insight():
    """
    Test the key insight: When m is both upper bound and in the list,
    it must be the unique maximum (or tied for maximum).
    """
    print("\n=== Key Insight: m is upper bound and in list => m is maximum ===")

    test_cases = []

    # Generate test cases
    for _ in range(50):
        size = random.randint(1, 8)
        xs = [random.randint(-50, 50) for _ in range(size)]
        m = max(xs)  # Choose m as the maximum
        test_cases.append((xs, m))

    failures = 0
    total = 0

    for xs, m in test_cases:
        # Verify preconditions
        if not is_upper_bound(m, xs) or m not in xs:
            continue

        total += 1
        actual_max = max(xs)

        if m != actual_max:
            failures += 1
            print(f"FAIL: xs={xs}, m={m}, actual_max={actual_max}")
        else:
            print(f"PASS: xs={xs}, m={m} is indeed the maximum")

    print(f"Key Insight Results: {total - failures}/{total} tests passed")
    return failures == 0

if __name__ == "__main__":
    print("Testing subgoals for fold_right_max_inf_returns_max lemma")
    print("=" * 70)

    success1 = test_subgoal_1_lower_bound()
    success2 = test_subgoal_2_upper_bound()
    success3 = test_subgoal_3_equality()
    success4 = test_key_insight()

    print("\n" + "=" * 70)
    print("SUMMARY:")
    print(f"Subgoal 1 (lower bound): {'✅ PASS' if success1 else '❌ FAIL'}")
    print(f"Subgoal 2 (upper bound): {'✅ PASS' if success2 else '❌ FAIL'}")
    print(f"Subgoal 3 (equality): {'✅ PASS' if success3 else '❌ FAIL'}")
    print(f"Key Insight: {'✅ PASS' if success4 else '❌ FAIL'}")

    if all([success1, success2, success3, success4]):
        print("\n✅ All subgoals verified! Ready to proceed with Coq proof.")
        print("Strategy: Prove that m is the maximum, then use fold_right_max properties.")
    else:
        print("\n❌ Some subgoals failed. Need to review the lemma or implementation.")