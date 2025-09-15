#!/usr/bin/env python3
"""
Test script to verify the nonNegSum_inits_eq_fold_right lemma:

forall (ys : list Z),
  nonNegMaximum (map nonNegSum (inits ys)) = fold_right nonNegPlus 0 ys

Where:
- nonNegPlus(x, y) = max(0, x + y)
- nonNegSum(xs) = fold_left nonNegPlus xs 0
- nonNegMaximum(xs) = fold_right max 0 xs
- inits(xs) = all prefixes of xs
- fold_right nonNegPlus 0 ys = fold from right with nonNegPlus
"""

import random
import itertools
from typing import List

def non_neg_plus(x: int, y: int) -> int:
    """nonNegPlus(x, y) = max(0, x + y)"""
    return max(0, x + y)

def non_neg_sum_fold_left(xs: List[int]) -> int:
    """nonNegSum(xs) = fold_left nonNegPlus xs 0"""
    result = 0
    for x in xs:
        result = non_neg_plus(result, x)
    return result

def non_neg_maximum(xs: List[int]) -> int:
    """nonNegMaximum(xs) = fold_right max 0 xs"""
    result = 0
    for x in reversed(xs):
        result = max(x, result)
    return result

def inits(xs: List[int]) -> List[List[int]]:
    """Return all prefixes of xs, including empty list"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def fold_right_non_neg_plus(xs: List[int]) -> int:
    """fold_right nonNegPlus 0 xs"""
    result = 0
    for x in reversed(xs):
        result = non_neg_plus(x, result)
    return result

def test_lemma(ys: List[int]) -> bool:
    """Test if the lemma holds for a given list ys"""
    # Left side: nonNegMaximum (map nonNegSum (inits ys))
    prefixes = inits(ys)
    non_neg_sums = [non_neg_sum_fold_left(prefix) for prefix in prefixes]
    left_side = non_neg_maximum(non_neg_sums)

    # Right side: fold_right nonNegPlus 0 ys
    right_side = fold_right_non_neg_plus(ys)

    return left_side == right_side

def test_lemma_verbose(ys: List[int]) -> tuple:
    """Test lemma and return detailed breakdown"""
    prefixes = inits(ys)
    non_neg_sums = [non_neg_sum_fold_left(prefix) for prefix in prefixes]
    left_side = non_neg_maximum(non_neg_sums)
    right_side = fold_right_non_neg_plus(ys)

    return (
        left_side == right_side,
        left_side,
        right_side,
        prefixes,
        non_neg_sums
    )

def demonstrate_computation():
    """Show step-by-step computation for small examples"""
    print("=== Step-by-step demonstration ===")
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, -1],
        [-1, 2],
        [3, -2, 1],
        [-5, 3, 2],
        [1, 2, 3],
        [-1, -2, -3],
        [5, -10, 3, 2]
    ]

    for ys in test_cases:
        is_equal, left, right, prefixes, sums = test_lemma_verbose(ys)
        status = "✓" if is_equal else "✗"

        print(f"\n{status} ys = {ys}")
        print(f"  inits(ys) = {prefixes}")
        print(f"  map nonNegSum = {sums}")
        print(f"  nonNegMaximum = {left}")
        print(f"  fold_right nonNegPlus 0 = {right}")
        if not is_equal:
            print(f"  *** MISMATCH: {left} ≠ {right} ***")

def comprehensive_test():
    """Run comprehensive tests"""
    print("\n=== Comprehensive Testing ===")

    # Test small values systematically
    print("--- Systematic test on small lists ---")
    failed_cases = []
    total_tests = 0

    # Test all combinations of lists up to length 4 with values in [-3, 3]
    for length in range(5):  # lengths 0 to 4
        for values in itertools.product(range(-3, 4), repeat=length):
            ys = list(values)
            total_tests += 1

            if not test_lemma(ys):
                failed_cases.append(ys)
                if len(failed_cases) <= 10:  # Show first 10 failures
                    is_equal, left, right, prefixes, sums = test_lemma_verbose(ys)
                    print(f"FAIL: {ys} -> {left} ≠ {right}")

    print(f"Systematic tests: {total_tests - len(failed_cases)}/{total_tests} passed")
    if failed_cases:
        print(f"Failed cases: {len(failed_cases)}")
    else:
        print("All systematic tests PASSED!")

    # Random testing with larger values
    print("\n--- Random testing with larger values ---")
    random_failures = 0
    random_tests = 5000

    for _ in range(random_tests):
        length = random.randint(0, 10)
        ys = [random.randint(-20, 20) for _ in range(length)]

        if not test_lemma(ys):
            random_failures += 1
            if random_failures <= 5:  # Show first 5 random failures
                is_equal, left, right, prefixes, sums = test_lemma_verbose(ys)
                print(f"RANDOM FAIL: {ys} -> {left} ≠ {right}")

    print(f"Random tests: {random_tests - random_failures}/{random_tests} passed")
    if random_failures == 0:
        print("All random tests PASSED!")

    # Edge cases
    print("\n--- Edge case testing ---")
    edge_cases = [
        [],                          # empty list
        [0],                         # single zero
        [1],                         # single positive
        [-1],                        # single negative
        [0, 0, 0],                   # all zeros
        [1, 1, 1],                   # all positive
        [-1, -1, -1],                # all negative
        [10, -10],                   # cancel out
        [-10, 10],                   # negative then positive
        [5, -3, -1, 2],              # mixed values
        [100, -200, 50, 25],         # larger values
        list(range(1, 6)),           # [1,2,3,4,5]
        list(range(-5, 1)),          # [-5,-4,-3,-2,-1,0]
    ]

    edge_failures = []
    for ys in edge_cases:
        is_equal, left, right, prefixes, sums = test_lemma_verbose(ys)
        if not is_equal:
            edge_failures.append(ys)
            print(f"EDGE FAIL: {ys} -> {left} ≠ {right}")
        else:
            print(f"EDGE PASS: {ys} -> {left} = {right}")

    if not edge_failures:
        print("All edge cases PASSED!")

    # Summary
    total_failures = len(failed_cases) + random_failures + len(edge_failures)
    total_all_tests = total_tests + random_tests + len(edge_cases)

    print(f"\n=== SUMMARY ===")
    print(f"Total tests run: {total_all_tests}")
    print(f"Total failures: {total_failures}")

    if total_failures == 0:
        print("🎉 nonNegSum_inits_eq_fold_right lemma IS TRUE!")
        print("This confirms we can prove the lemma in Coq.")
    else:
        print("❌ nonNegSum_inits_eq_fold_right lemma is FALSE")
        print("Cannot prove the lemma in Coq - it's mathematically false!")

    return total_failures == 0

def analyze_pattern():
    """Analyze the mathematical pattern to understand why it works/fails"""
    print("\n=== Pattern Analysis ===")

    # Test if there's a pattern in when it works vs fails
    print("Looking for patterns in successes/failures...")

    # Test some specific patterns
    patterns = [
        ("All positive", [[1, 2, 3], [2, 4, 6], [1, 3, 5]]),
        ("All negative", [[-1, -2, -3], [-2, -4, -6], [-1, -3, -5]]),
        ("Mixed balanced", [[1, -1], [2, -2], [3, -3]]),
        ("Alternating", [[1, -1, 1], [-1, 1, -1], [2, -1, 2]]),
        ("Increasing", [[1, 2, 3, 4], [0, 1, 2, 3], [-2, -1, 0, 1]]),
        ("Decreasing", [[4, 3, 2, 1], [3, 2, 1, 0], [1, 0, -1, -2]]),
    ]

    for pattern_name, test_lists in patterns:
        all_pass = True
        for ys in test_lists:
            if not test_lemma(ys):
                all_pass = False
                break
        print(f"{pattern_name}: {'PASS' if all_pass else 'FAIL'}")

if __name__ == "__main__":
    demonstrate_computation()
    analyze_pattern()
    is_true = comprehensive_test()

    if is_true:
        print("\n✅ Ready to prove nonNegSum_inits_eq_fold_right in Coq!")
    else:
        print("\n❌ Cannot prove nonNegSum_inits_eq_fold_right - the lemma is false!")
        print("Need to reconsider the mathematical approach.")