#!/usr/bin/env python3
"""
Test logical consistency and search for subtle counterexamples in TropicalMaxSegSum.v
"""

import itertools
from typing import List, Tuple, Optional

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

def mixed_signs(xs: List[int]) -> bool:
    return not all(x >= 0 for x in xs) and not all(x <= 0 for x in xs)

def test_logical_consistency_deep(xs: List[int]) -> List[str]:
    """Deep logical consistency test for all admitted lemmas together"""
    if not mixed_signs(xs):
        return []

    issues = []
    prefixes = inits(xs)

    # Compute all relevant values
    regular_sums = [fold_right_add(p) for p in prefixes]
    nonNeg_sums = [fold_right_nonNegPlus(p) for p in prefixes]

    max_regular = fold_right_max(regular_sums)
    max_nonNeg = fold_right_max(nonNeg_sums)
    full_nonNeg = fold_right_nonNegPlus(xs)

    # Test 1: Main theorem (maxsegsum_mixed_case)
    if full_nonNeg != max_nonNeg:
        issues.append(f"Main theorem fails: nonNegSum({xs}) = {full_nonNeg} != {max_nonNeg}")

    # Test 2: maximum_equivalence_in_mixed_case
    if max_regular != max_nonNeg:
        issues.append(f"Maximum equivalence fails: max_regular = {max_regular} != {max_nonNeg} = max_nonNeg")

    # Test 3: exists_nonneg_maximizing_prefix (when max_regular >= 0)
    if max_regular >= 0:
        found_nonneg_maximizer = False
        for i, p in enumerate(prefixes):
            p_sum = regular_sums[i]
            if p_sum == max_regular and p_sum >= 0:
                found_nonneg_maximizer = True
                break

        if not found_nonneg_maximizer:
            issues.append(f"No nonnegative prefix achieves maximum {max_regular}")

    # Test 4: maximum_prefix_equality (for maximizing prefixes)
    for i, p in enumerate(prefixes):
        if regular_sums[i] == max_regular:
            if nonNeg_sums[i] != regular_sums[i]:
                issues.append(f"Prefix equality fails: prefix {p} has regular={regular_sums[i]}, nonNeg={nonNeg_sums[i]}")

    # Additional consistency checks
    # Check that nonNegPlus is always >= regular addition for each prefix
    for i, p in enumerate(prefixes):
        if nonNeg_sums[i] < regular_sums[i]:
            issues.append(f"NonNeg sum smaller than regular: prefix {p}, nonNeg={nonNeg_sums[i]}, regular={regular_sums[i]}")

    # Check that maximum is actually achieved
    if max_regular not in regular_sums:
        issues.append(f"Maximum {max_regular} not achieved by any prefix")

    if max_nonNeg not in nonNeg_sums:
        issues.append(f"NonNeg maximum {max_nonNeg} not achieved by any prefix")

    return issues

def find_problematic_patterns():
    """Look for patterns that might cause issues"""
    print("Searching for potentially problematic patterns...")

    # Test cases where the nonNegPlus behavior might be tricky
    tricky_cases = []

    # Cases where prefix sums go deeply negative then recover
    for neg_depth in range(-10, -1):
        for recovery in range(1, 15):
            if recovery > abs(neg_depth):  # Recovery is larger than the negative
                cases = [
                    [neg_depth, recovery],
                    [1, neg_depth, recovery],
                    [neg_depth, recovery, -1],
                    [1, neg_depth, recovery, -1],
                    [neg_depth, recovery // 2, recovery // 2],
                ]
                for case in cases:
                    if mixed_signs(case):
                        tricky_cases.append(case)

    # Test all tricky cases
    all_issues = []
    for xs in tricky_cases:
        issues = test_logical_consistency_deep(xs)
        if issues:
            all_issues.append((xs, issues))

    return all_issues

def test_boundary_conditions():
    """Test boundary conditions that might expose issues"""
    print("Testing boundary conditions...")

    boundary_cases = []

    # Cases where sums equal zero at critical points
    boundary_cases.extend([
        [-1, 1],                # Sum to zero
        [-2, 2],                # Sum to zero
        [2, -2],                # Sum to zero
        [1, -1, 1, -1],         # Alternating sum to zero
        [3, -3, 1],             # Zero then positive
        [-3, 3, -1],            # Zero then negative
        [5, -3, -2],            # Positive then sum to zero
        [-5, 3, 2],             # Negative then sum to zero
    ])

    # Cases with very large numbers
    boundary_cases.extend([
        [-1000, 1001],          # Large recovery
        [1000, -1001],          # Large crash
        [-500, 250, 250],       # Exact recovery over two steps
        [100, -200, 101],       # Slight over-recovery
    ])

    all_issues = []
    for xs in boundary_cases:
        if mixed_signs(xs):
            issues = test_logical_consistency_deep(xs)
            if issues:
                all_issues.append((xs, issues))

    return all_issues

def main():
    """Main testing function"""
    print("=" * 80)
    print("LOGICAL CONSISTENCY AND DEEP COUNTEREXAMPLE SEARCH")
    print("=" * 80)

    # Test 1: Problematic patterns
    pattern_issues = find_problematic_patterns()

    if pattern_issues:
        print("❌ Issues found in problematic patterns:")
        for xs, issues in pattern_issues:
            print(f"  Case {xs}:")
            for issue in issues:
                print(f"    - {issue}")
    else:
        print("✅ No issues found in problematic patterns")

    # Test 2: Boundary conditions
    boundary_issues = test_boundary_conditions()

    if boundary_issues:
        print("❌ Issues found in boundary conditions:")
        for xs, issues in boundary_issues:
            print(f"  Case {xs}:")
            for issue in issues:
                print(f"    - {issue}")
    else:
        print("✅ No issues found in boundary conditions")

    # Test 3: Exhaustive small cases
    print("\nTesting exhaustive small mixed-sign cases...")
    small_issues = []

    for length in range(2, 5):  # Test lengths 2, 3, 4
        for values in itertools.product(range(-5, 6), repeat=length):
            xs = list(values)
            if mixed_signs(xs) and 0 not in xs:  # Exclude zero for cleaner mixed-sign test
                issues = test_logical_consistency_deep(xs)
                if issues:
                    small_issues.append((xs, issues))

    if small_issues:
        print(f"❌ Issues found in {len(small_issues)} small cases:")
        for xs, issues in small_issues[:10]:  # Show first 10 issues
            print(f"  Case {xs}:")
            for issue in issues:
                print(f"    - {issue}")
        if len(small_issues) > 10:
            print(f"  ... and {len(small_issues) - 10} more cases")
    else:
        print("✅ No issues found in exhaustive small cases")

    # Final summary
    print("\n" + "=" * 80)
    total_issues = len(pattern_issues) + len(boundary_issues) + len(small_issues)

    if total_issues > 0:
        print(f"❌ TOTAL: {total_issues} logical inconsistencies found!")
        print("Some admitted lemmas may be false and need proofs of falsity.")
    else:
        print("✅ COMPREHENSIVE TEST PASSED: No logical inconsistencies found.")
        print("All admitted lemmas appear to be correct based on computational verification.")

if __name__ == "__main__":
    main()