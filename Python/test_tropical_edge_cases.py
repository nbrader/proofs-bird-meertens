#!/usr/bin/env python3
"""
Additional edge case testing for admitted lemmas in TropicalMaxSegSum.v

This script tests edge cases and potentially problematic patterns.
"""

import random
from typing import List, Optional

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

def mixed_signs(xs: List[int]) -> bool:
    """Check if neither all non-negative nor all non-positive"""
    return not all(x >= 0 for x in xs) and not all(x <= 0 for x in xs)

def test_maxsegsum_mixed_case(xs: List[int]) -> Optional[str]:
    """
    Test the main theorem: maxsegsum_mixed_case
    """
    if not mixed_signs(xs):
        return None

    left_side = fold_right_nonNegPlus(xs)

    prefixes = inits(xs)
    prefix_nonNeg_sums = [fold_right_nonNegPlus(p) for p in prefixes]
    right_side = fold_right_max(prefix_nonNeg_sums)

    if left_side != right_side:
        return f"COUNTEREXAMPLE: {xs}, left={left_side}, right={right_side}"

    return None

def generate_edge_cases() -> List[List[int]]:
    """Generate edge cases that might break the theorem"""
    edge_cases = []

    # Cases with large negative values followed by smaller positives
    edge_cases.extend([
        [-10, 1, 1, 1, 1],      # Large negative, multiple small positives
        [-5, 2, 2],             # Medium negative, medium positives
        [-100, 50, 50],         # Very large negative, large positives that don't recover
        [-7, 3, 3, 1],          # Negative larger than sum of positives
    ])

    # Cases with alternating signs
    edge_cases.extend([
        [-1, 1, -1, 1, -1],     # Strict alternating
        [-2, 1, -2, 1, -2],     # Alternating with negative bias
        [1, -2, 1, -2, 1],      # Alternating with positive start
        [-3, 2, -3, 2, -3, 2],  # Longer alternating
    ])

    # Cases with complex patterns
    edge_cases.extend([
        [5, -10, 6],            # Positive, large negative, positive
        [-4, 10, -7],           # Negative, large positive, negative
        [2, -1, -1, -1, 3],     # Positive, multiple negatives, positive
        [-1, -1, -1, 5, -2],    # Multiple negatives, large positive, negative
        [1, 2, -10, 3, 4],      # Building positive, crash, rebuild
        [-3, -2, 8, -4],        # Multiple negatives, recovery, drop
    ])

    # Cases designed to test specific properties
    edge_cases.extend([
        # Cases where maximum might not be achieved by the full array
        [3, -5, 2],             # Best subarray is [3]
        [1, -3, 1, 1],          # Best might be [1, 1] at end
        [2, -4, 1, 2],          # Complex optimal subarray

        # Cases where nonNegPlus behavior might differ significantly
        [-1, -1, 4, -2, -2],    # Deep negative, recovery, decline
        [1, 1, -6, 2, 2, 1],    # Build up, crash, slow recovery
    ])

    # Random cases with specific properties
    random.seed(42)  # For reproducibility
    for _ in range(50):
        length = random.randint(3, 10)
        # Generate mixed-sign lists with bias toward problematic patterns
        xs = []
        for i in range(length):
            if random.random() < 0.5:
                # Negative value
                xs.append(random.randint(-10, -1))
            else:
                # Positive value
                xs.append(random.randint(1, 10))

        if mixed_signs(xs):
            edge_cases.append(xs)

    return edge_cases

def analyze_case_in_detail(xs: List[int]):
    """Provide detailed analysis of a specific case"""
    print(f"\nDetailed Analysis: {xs}")
    print("=" * 50)

    if not mixed_signs(xs):
        print("Not a mixed-signs case, skipping.")
        return

    prefixes = inits(xs)
    print(f"Prefixes: {prefixes}")

    # Compute prefix sums with both methods
    regular_sums = [fold_right_add(p) for p in prefixes]
    nonNeg_sums = [fold_right_nonNegPlus(p) for p in prefixes]

    print(f"Regular prefix sums: {regular_sums}")
    print(f"NonNeg prefix sums:  {nonNeg_sums}")

    max_regular = fold_right_max(regular_sums)
    max_nonNeg = fold_right_max(nonNeg_sums)

    print(f"Maximum regular sum: {max_regular}")
    print(f"Maximum nonNeg sum:  {max_nonNeg}")

    full_nonNeg = fold_right_nonNegPlus(xs)
    print(f"nonNegSum of full list: {full_nonNeg}")

    # Check the main theorem
    print(f"Main theorem: {full_nonNeg} == {max_nonNeg} ? {full_nonNeg == max_nonNeg}")

    # Find which prefixes achieve the maxima
    max_regular_indices = [i for i, s in enumerate(regular_sums) if s == max_regular]
    max_nonNeg_indices = [i for i, s in enumerate(nonNeg_sums) if s == max_nonNeg]

    print(f"Regular maximum achieved at indices: {max_regular_indices}")
    print(f"NonNeg maximum achieved at indices: {max_nonNeg_indices}")

    if max_regular_indices:
        idx = max_regular_indices[0]
        prefix = prefixes[idx]
        print(f"First regular max prefix: {prefix}")
        print(f"  Regular sum: {fold_right_add(prefix)}")
        print(f"  NonNeg sum:  {fold_right_nonNegPlus(prefix)}")

def main():
    """Run edge case tests"""
    edge_cases = generate_edge_cases()

    print(f"Testing {len(edge_cases)} edge cases for counterexamples...")
    print("=" * 80)

    counterexamples = []

    for xs in edge_cases:
        result = test_maxsegsum_mixed_case(xs)
        if result:
            counterexamples.append((xs, result))

    if counterexamples:
        print(f"❌ Found {len(counterexamples)} counterexamples:")
        for xs, msg in counterexamples:
            print(f"  {msg}")
            analyze_case_in_detail(xs)
    else:
        print("✅ No counterexamples found in edge cases!")

    # Analyze some interesting cases regardless
    print("\n" + "=" * 80)
    print("Analysis of some interesting edge cases:")

    interesting = [
        [-10, 1, 1, 1, 1],      # Large negative start
        [5, -10, 6],            # Positive, crash, recovery
        [1, 2, -10, 3, 4],      # Build, crash, rebuild
        [-1, -1, 4, -2, -2],    # Deep negative, recovery, decline
    ]

    for case in interesting:
        if mixed_signs(case):
            analyze_case_in_detail(case)

if __name__ == "__main__":
    main()