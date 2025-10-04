#!/usr/bin/env python3
"""
Test the maximum agreement point claim computationally.

The goal states that for mixed-sign lists, there exists an index j where:
1. The nonNegSum list achieves its maximum at position j
2. Both nonNegSum and regular sum give the same result at position j

Let's test this computationally.
"""

def non_neg_plus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def non_neg_sum(lst):
    """nonNegSum: fold_right nonNegPlus 0 lst"""
    result = 0
    for x in reversed(lst):
        result = non_neg_plus(x, result)
    return result

def sum_list(lst):
    """Regular sum of list"""
    return sum(lst)

def inits(lst):
    """Generate all initial segments (prefixes) of a list"""
    result = [[]]
    for i in range(len(lst)):
        result.append(lst[:i+1])
    return result

def mixed_signs(lst):
    """Check if list has mixed signs (both positive and negative elements)"""
    has_pos = any(x > 0 for x in lst)
    has_neg = any(x < 0 for x in lst)
    return has_pos and has_neg

def test_agreement_point():
    """Test the maximum agreement point claim"""

    print("=== Testing maximum agreement point existence ===")
    print()

    # Test cases with mixed signs
    test_cases = [
        [-1, 1],
        [-2, 1],
        [1, -1],
        [-1, 0, 1],
        [2, -3, 1],
        [-1, 2, -1],
        [3, -5, 2],
        [-2, 1, -1, 2],
        [-3, 2, -1, 3],
        [5, -2, -1, 4],
    ]

    agreements_found = 0
    total_cases = 0

    for xs in test_cases:
        if not mixed_signs(xs):
            continue

        total_cases += 1

        print(f"Testing xs = {xs}")

        # Compute all prefixes
        prefixes = inits(xs)
        print(f"  Prefixes: {prefixes}")

        # Compute nonNegSum for each prefix
        nonneg_sums = [non_neg_sum(p) for p in prefixes]
        print(f"  nonNegSums: {nonneg_sums}")

        # Compute regular sum for each prefix
        regular_sums = [sum_list(p) for p in prefixes]
        print(f"  Regular sums: {regular_sums}")

        # Find maximum of nonNegSum list
        max_nonneg = max(nonneg_sums)
        print(f"  Max nonNegSum: {max_nonneg}")

        # Find all indices where nonNegSum achieves its maximum
        max_indices = [i for i, val in enumerate(nonneg_sums) if val == max_nonneg]
        print(f"  Indices achieving max: {max_indices}")

        # Check if any of these indices has agreement between both methods
        agreement_found = False
        for j in max_indices:
            nonneg_at_j = nonneg_sums[j]
            regular_at_j = regular_sums[j]
            print(f"    At index {j}: nonNegSum={nonneg_at_j}, regular={regular_at_j}")

            if nonneg_at_j == regular_at_j:
                print(f"    *** AGREEMENT FOUND at index {j}! ***")
                agreement_found = True
                break

        if agreement_found:
            agreements_found += 1
            print(f"  ✅ Agreement point exists")
        else:
            print(f"  ❌ No agreement point found")

        print()

    print(f"Summary: {agreements_found}/{total_cases} mixed-sign cases have agreement points")

    if agreements_found == total_cases:
        print("✅ All mixed-sign cases have agreement points!")
        print("This supports the Coq goal that such a point always exists.")
    else:
        print("❌ Some cases lack agreement points.")
        print("The Coq goal may need refinement or additional constraints.")

def analyze_when_agreement_occurs():
    """Analyze the conditions under which agreement occurs"""

    print("=== Analyzing when agreement occurs ===")
    print()

    # Look for patterns in where agreement happens
    test_cases = [
        [-1, 1],
        [-2, 1],
        [-3, 1],
        [1, -1],
        [2, -1],
        [3, -1],
        [-1, 2],
        [-2, 3],
        [-1, 2, -1],
        [2, -1, 1],
    ]

    for xs in test_cases:
        if not mixed_signs(xs):
            continue

        prefixes = inits(xs)
        nonneg_sums = [non_neg_sum(p) for p in prefixes]
        regular_sums = [sum_list(p) for p in prefixes]

        max_nonneg = max(nonneg_sums)
        max_indices = [i for i, val in enumerate(nonneg_sums) if val == max_nonneg]

        print(f"xs = {xs}")
        print(f"  Max achieved at indices: {max_indices}")

        for j in max_indices:
            prefix = prefixes[j]
            nonneg_val = nonneg_sums[j]
            regular_val = regular_sums[j]

            print(f"    Index {j}: prefix={prefix}, nonNeg={nonneg_val}, regular={regular_val}")

            if nonneg_val == regular_val:
                print(f"      → Agreement! Prefix sum is non-negative: {regular_val >= 0}")
            else:
                print(f"      → No agreement. Difference: {nonneg_val - regular_val}")
        print()

if __name__ == "__main__":
    test_agreement_point()
    analyze_when_agreement_occurs()