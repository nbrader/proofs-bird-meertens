#!/usr/bin/env python3
"""
Test a key property that can help us prove the lemma without circular dependencies.

Property: If m is an upper bound and in the list, then m is the maximum element.
This is simpler to prove and doesn't require the fold_right_max_inf_in lemma.
"""

from typing import Union, List
import random

def test_upper_bound_in_list_is_max():
    """
    Test: If m is in xs and m is an upper bound for all elements in xs,
    then m = max(xs).

    This is a fundamental property we can prove directly without dependencies.
    """
    print("Testing: upper bound + membership => maximum element")

    test_cases = []

    # Simple test cases
    test_cases.extend([
        ([1], 1),
        ([1, 2], 2),
        ([2, 1], 2),
        ([1, 2, 3], 3),
        ([3, 2, 1], 3),
        ([-1, -2, -3], -1),
        ([5, 5, 5], 5),
        ([0, 1, -1], 1),
    ])

    # Generate random test cases
    for _ in range(50):
        size = random.randint(1, 10)
        xs = [random.randint(-100, 100) for _ in range(size)]
        m = max(xs)  # m is definitely the maximum
        test_cases.append((xs, m))

    failures = 0
    total = 0

    for xs, m in test_cases:
        # Check preconditions: m is in xs and is upper bound
        if m not in xs:
            continue

        is_upper_bound = all(y <= m for y in xs)
        if not is_upper_bound:
            continue

        total += 1
        actual_max = max(xs)

        if m != actual_max:
            failures += 1
            print(f"FAIL: xs={xs}, m={m}, actual_max={actual_max}")
        else:
            print(f"PASS: xs={xs}, m={m} is the maximum")

    print(f"\nResults: {total - failures}/{total} tests passed")
    return failures == 0

def test_max_element_gives_max_fold():
    """
    Test: If m = max(xs), then fold_right_max(xs) = m

    This is much simpler than the general case.
    """
    print("\nTesting: m = max(xs) => fold_right_max(xs) = m")

    # Type definitions for fold_right max
    class NegInf:
        def __repr__(self):
            return "NegInf"
        def __eq__(self, other):
            return isinstance(other, NegInf)

    def z_plus_neg_inf_max(x, y):
        if isinstance(x, NegInf):
            return y
        if isinstance(y, NegInf):
            return x
        return max(x, y)

    def fold_right_max_inf(xs):
        if not xs:
            return NegInf()
        result = NegInf()
        for x in reversed(xs):
            result = z_plus_neg_inf_max(x, result)
        return result

    test_cases = [
        [1], [1, 2], [2, 1], [1, 2, 3], [3, 2, 1],
        [-1, -2, -3], [5, 5, 5], [0, 1, -1]
    ]

    # Add random cases
    for _ in range(30):
        size = random.randint(1, 8)
        xs = [random.randint(-50, 50) for _ in range(size)]
        test_cases.append(xs)

    failures = 0
    total = 0

    for xs in test_cases:
        if not xs:
            continue

        total += 1
        m = max(xs)
        result = fold_right_max_inf(xs)

        if isinstance(result, NegInf):
            failures += 1
            print(f"FAIL: xs={xs}, expected {m}, got NegInf")
        elif result != m:
            failures += 1
            print(f"FAIL: xs={xs}, expected {m}, got {result}")
        else:
            print(f"PASS: xs={xs}, max={m}, result={result}")

    print(f"\nResults: {total - failures}/{total} tests passed")
    return failures == 0

if __name__ == "__main__":
    print("Testing simplified properties for fold_right_max_inf lemma")
    print("=" * 60)

    success1 = test_upper_bound_in_list_is_max()
    success2 = test_max_element_gives_max_fold()

    print("\n" + "=" * 60)
    print("SUMMARY:")
    print(f"Upper bound + membership => maximum: {'✅ PASS' if success1 else '❌ FAIL'}")
    print(f"Maximum element gives max fold: {'✅ PASS' if success2 else '❌ FAIL'}")

    if success1 and success2:
        print("\n✅ Both simplified properties verified!")
        print("Strategy: Prove m = max(xs), then use simpler max fold property.")
    else:
        print("\n❌ Some properties failed.")