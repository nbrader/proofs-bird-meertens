#!/usr/bin/env python3
"""
Analyze the major discrepancy found: nonNegSum vs maximum subarray sum

This investigates the issue found in tropical finite preservation test.
"""

from typing import List

def nonNegPlus(x: int, y: int) -> int:
    return max(x + y, 0)

def fold_right_nonNegPlus(xs: List[int]) -> int:
    result = 0
    for x in reversed(xs):
        result = nonNegPlus(x, result)
    return result

def fold_right_add(xs: List[int]) -> int:
    return sum(xs)

def fold_right_max(xs: List[int]) -> int:
    result = 0
    for x in reversed(xs):
        result = max(x, result)
    return result

def inits(xs: List[int]) -> List[List[int]]:
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def max_subarray_sum(xs: List[int]) -> int:
    """Classical Kadane's algorithm - maximum sum of any contiguous subarray"""
    if not xs:
        return 0

    max_so_far = xs[0]
    max_ending_here = xs[0]

    for i in range(1, len(xs)):
        max_ending_here = max(xs[i], max_ending_here + xs[i])
        max_so_far = max(max_so_far, max_ending_here)

    return max_so_far

def max_prefix_sum(xs: List[int]) -> int:
    """Maximum sum of any prefix (what the admitted lemmas are about)"""
    prefix_sums = [fold_right_add(p) for p in inits(xs)]
    return fold_right_max(prefix_sums)

def analyze_discrepancy():
    """Analyze the discrepancy between different interpretations"""

    test_cases = [
        [-5, 1],
        [-5, 2],
        [1, -3, 2],
        [-2, 4, -1],
        [-1, -1, 3],
        [2, -5, 3, 1],
    ]

    print("Analysis of nonNegSum vs Maximum Subarray Problem")
    print("=" * 80)
    print("Key insight: nonNegSum ≠ maximum subarray sum!")
    print("nonNegSum computes something related to prefix sums, not subarrays.")
    print()

    for xs in test_cases:
        print(f"Input: {xs}")
        print("-" * 40)

        # All the different interpretations
        nonNeg_result = fold_right_nonNegPlus(xs)
        max_subarray = max_subarray_sum(xs)
        max_prefix = max_prefix_sum(xs)
        clamped_max_subarray = max(0, max_subarray)
        clamped_max_prefix = max(0, max_prefix)

        print(f"  nonNegSum(xs):           {nonNeg_result}")
        print(f"  max subarray sum:        {max_subarray}")
        print(f"  max prefix sum:          {max_prefix}")
        print(f"  max(0, max_subarray):    {clamped_max_subarray}")
        print(f"  max(0, max_prefix):      {clamped_max_prefix}")

        # Check what nonNegSum actually equals
        prefix_nonNegSums = [fold_right_nonNegPlus(p) for p in inits(xs)]
        max_prefix_nonNeg = fold_right_max(prefix_nonNegSums)

        print(f"  max(nonNegSum(prefixes)): {max_prefix_nonNeg}")

        # Show prefix details
        prefixes = inits(xs)
        prefix_regular_sums = [sum(p) for p in prefixes]

        print(f"  Prefixes: {prefixes}")
        print(f"  Regular prefix sums: {prefix_regular_sums}")
        print(f"  NonNeg prefix sums:  {prefix_nonNegSums}")

        # The key insight: What is nonNegSum actually computing?
        print(f"  INSIGHT: nonNegSum = max(nonNegSum(prefixes)) ? {nonNeg_result == max_prefix_nonNeg}")
        print()

def verify_kadane_vs_prefix_interpretation():
    """Verify which interpretation is correct for the file's goals"""

    print("\nVerifying the file's actual goals:")
    print("=" * 50)

    # The file claims: nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))
    # This is about PREFIX sums, not general subarray sums!

    test_cases = [
        [-1, 2, -1],
        [1, -2, 3],
        [-2, 3, -1],
        [2, -3, 1, -1]
    ]

    for xs in test_cases:
        print(f"\nCase: {xs}")

        # Left side of the equation in the file
        left_side = fold_right_nonNegPlus(xs)

        # Right side of the equation in the file
        prefixes = inits(xs)
        prefix_nonNegSums = [fold_right_nonNegPlus(p) for p in prefixes]
        right_side = fold_right_max(prefix_nonNegSums)

        print(f"  nonNegSum(xs) = {left_side}")
        print(f"  max(map nonNegSum (inits xs)) = {right_side}")
        print(f"  Equal? {left_side == right_side}")

        if left_side != right_side:
            print(f"  ❌ COUNTEREXAMPLE to main theorem!")
            print(f"     Prefixes: {prefixes}")
            print(f"     Prefix nonNegSums: {prefix_nonNegSums}")
            return xs

    print("\n✅ All test cases satisfy the main theorem (about prefixes)")
    return None

if __name__ == "__main__":
    analyze_discrepancy()
    counterexample = verify_kadane_vs_prefix_interpretation()

    if counterexample:
        print(f"\n🚨 MAJOR ISSUE: Found counterexample {counterexample} to the main theorem!")
    else:
        print(f"\n✅ The admitted lemmas are about PREFIX sums, not general subarray sums.")
        print("The 'tropical finite preservation' failures were due to testing wrong property.")