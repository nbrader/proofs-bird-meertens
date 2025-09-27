#!/usr/bin/env python3
"""
Test for counterexamples to admitted lemmas in TropicalMaxSegSum.v

This script tests the following admitted lemmas for counterexamples:
1. exists_nonneg_maximizing_prefix
2. maximum_prefix_equality
3. maximum_equivalence_in_mixed_case
4. maxsegsum_mixed_case
"""

import itertools
from typing import List, Tuple, Optional

def nonNegPlus(x: int, y: int) -> int:
    """nonNegPlus x y = max(x + y, 0)"""
    return max(x + y, 0)

def fold_right_nonNegPlus(xs: List[int]) -> int:
    """fold_right nonNegPlus 0 xs"""
    result = 0
    for x in reversed(xs):
        result = nonNegPlus(x, result)
    return result

def fold_right_add(xs: List[int]) -> int:
    """fold_right Z.add 0 xs = sum(xs)"""
    return sum(xs)

def fold_right_max(xs: List[int]) -> int:
    """fold_right Z.max 0 xs"""
    result = 0
    for x in reversed(xs):
        result = max(x, result)
    return result

def inits(xs: List[int]) -> List[List[int]]:
    """All initial segments of xs"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def all_nonnegative(xs: List[int]) -> bool:
    """Check if all elements are >= 0"""
    return all(x >= 0 for x in xs)

def all_nonpositive(xs: List[int]) -> bool:
    """Check if all elements are <= 0"""
    return all(x <= 0 for x in xs)

def mixed_signs(xs: List[int]) -> bool:
    """Check if neither all non-negative nor all non-positive"""
    return not all_nonnegative(xs) and not all_nonpositive(xs)

def test_exists_nonneg_maximizing_prefix(xs: List[int]) -> Optional[str]:
    """
    Test: exists_nonneg_maximizing_prefix

    For mixed_signs xs with max >= 0, there should exist a prefix p where:
    - p is in inits(xs)
    - fold_right Z.add 0 p = M (the maximum)
    - 0 <= fold_right Z.add 0 p
    """
    if not mixed_signs(xs):
        return None

    prefix_sums = [fold_right_add(p) for p in inits(xs)]
    M = fold_right_max(prefix_sums)

    if M < 0:
        return None  # Lemma only applies when M >= 0

    # Check if there exists a prefix achieving the maximum with nonnegative sum
    for p in inits(xs):
        p_sum = fold_right_add(p)
        if p_sum == M and p_sum >= 0:
            return None  # Found such a prefix, lemma holds

    return f"Counterexample: {xs}, M={M}, no nonnegative prefix achieves maximum"

def test_maximum_prefix_equality(xs: List[int]) -> Optional[str]:
    """
    Test: maximum_prefix_equality

    For mixed_signs xs, if p achieves the maximum, then:
    fold_right nonNegPlus 0 p = fold_right Z.add 0 p
    """
    if not mixed_signs(xs):
        return None

    prefix_sums = [fold_right_add(p) for p in inits(xs)]
    M = fold_right_max(prefix_sums)

    for p in inits(xs):
        p_sum = fold_right_add(p)
        if p_sum == M:  # p achieves the maximum
            nonNeg_sum = fold_right_nonNegPlus(p)
            if nonNeg_sum != p_sum:
                return f"Counterexample: {xs}, prefix {p}, nonNegPlus={nonNeg_sum}, add={p_sum}"

    return None

def test_maximum_equivalence_in_mixed_case(xs: List[int]) -> Optional[str]:
    """
    Test: maximum_equivalence_in_mixed_case

    For mixed_signs xs:
    fold_right Z.max 0 (map (fold_right nonNegPlus 0) (inits xs)) =
    fold_right Z.max 0 (map (fold_right Z.add 0) (inits xs))
    """
    if not mixed_signs(xs):
        return None

    prefixes = inits(xs)
    nonNeg_sums = [fold_right_nonNegPlus(p) for p in prefixes]
    regular_sums = [fold_right_add(p) for p in prefixes]

    max_nonNeg = fold_right_max(nonNeg_sums)
    max_regular = fold_right_max(regular_sums)

    if max_nonNeg != max_regular:
        return f"Counterexample: {xs}, max_nonNeg={max_nonNeg}, max_regular={max_regular}"

    return None

def test_maxsegsum_mixed_case(xs: List[int]) -> Optional[str]:
    """
    Test: maxsegsum_mixed_case

    For mixed_signs xs:
    nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))

    where nonNegSum = fold_right nonNegPlus 0
    and nonNegMaximum = fold_right Z.max 0
    """
    if not mixed_signs(xs):
        return None

    left_side = fold_right_nonNegPlus(xs)

    prefixes = inits(xs)
    prefix_nonNeg_sums = [fold_right_nonNegPlus(p) for p in prefixes]
    right_side = fold_right_max(prefix_nonNeg_sums)

    if left_side != right_side:
        return f"Counterexample: {xs}, left={left_side}, right={right_side}"

    return None

def generate_test_cases() -> List[List[int]]:
    """Generate comprehensive test cases"""
    test_cases = []

    # Small lists with mixed signs
    for length in range(1, 6):
        for combo in itertools.product([-3, -2, -1, 1, 2, 3], repeat=length):
            xs = list(combo)
            if mixed_signs(xs):
                test_cases.append(xs)

    # Some specific potentially problematic cases
    additional_cases = [
        [-1, 2, -1],           # Simple mixed case
        [1, -2, 3],            # Mixed with positive maximum
        [-2, 3, -1],           # Mixed starting negative
        [2, -3, 1, -1],        # Longer mixed case
        [-1, -1, 3, -2],       # Multiple negatives then positive
        [1, 1, -5, 2, 2],      # Positive start, big negative, positive end
        [-3, 4, -2, 1],        # Pattern that might break equality
        [2, -1, -1, 2],        # Symmetric mixed case
        [-2, 5, -3],           # Large positive bounded by negatives
        [3, -4, 2, -1],        # Descending pattern
    ]

    for case in additional_cases:
        if mixed_signs(case):
            test_cases.append(case)

    return test_cases

def main():
    """Run all tests and report counterexamples"""
    test_cases = generate_test_cases()

    print(f"Testing {len(test_cases)} mixed-sign cases for counterexamples...")
    print("=" * 80)

    tests = [
        ("exists_nonneg_maximizing_prefix", test_exists_nonneg_maximizing_prefix),
        ("maximum_prefix_equality", test_maximum_prefix_equality),
        ("maximum_equivalence_in_mixed_case", test_maximum_equivalence_in_mixed_case),
        ("maxsegsum_mixed_case", test_maxsegsum_mixed_case),
    ]

    counterexamples_found = False

    for test_name, test_func in tests:
        print(f"\nTesting {test_name}:")
        print("-" * 40)

        found_counter = False
        for xs in test_cases:
            result = test_func(xs)
            if result:
                print(f"  ❌ {result}")
                found_counter = True
                counterexamples_found = True

        if not found_counter:
            print(f"  ✅ No counterexamples found in {len(test_cases)} test cases")

    print("\n" + "=" * 80)
    if counterexamples_found:
        print("❌ COUNTEREXAMPLES FOUND! Some admitted lemmas may be false.")
    else:
        print("✅ No counterexamples found. Admitted lemmas appear correct on tested cases.")

    # Additional detailed analysis for specific interesting cases
    print("\nDetailed analysis for some specific cases:")
    print("-" * 50)

    interesting_cases = [
        [-1, 2, -1],
        [1, -2, 3],
        [-2, 3, -1],
        [2, -3, 1, -1]
    ]

    for xs in interesting_cases:
        if mixed_signs(xs):
            print(f"\nCase: {xs}")
            prefixes = inits(xs)
            print(f"  Prefixes: {prefixes}")

            regular_sums = [fold_right_add(p) for p in prefixes]
            nonNeg_sums = [fold_right_nonNegPlus(p) for p in prefixes]

            print(f"  Regular sums: {regular_sums}")
            print(f"  NonNeg sums:  {nonNeg_sums}")
            print(f"  Max regular:  {fold_right_max(regular_sums)}")
            print(f"  Max nonNeg:   {fold_right_max(nonNeg_sums)}")
            print(f"  nonNegSum(xs): {fold_right_nonNegPlus(xs)}")

if __name__ == "__main__":
    main()