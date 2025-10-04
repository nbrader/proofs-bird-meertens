#!/usr/bin/env python3
"""
Test the maximum_equivalence_in_mixed_case lemma computationally.

The lemma claims that for mixed-sign lists:
fold_right Z.max 0 (map nonNegSum (inits xs)) =
fold_right Z.max 0 (map (fun p -> max(0, sum(p))) (inits xs))

Let's test this computationally and find where the proof breaks down.
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

def test_maximum_equivalence():
    """Test the maximum equivalence claim"""

    print("=== Testing maximum_equivalence_in_mixed_case ===")
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
    ]

    for xs in test_cases:
        if not mixed_signs(xs):
            continue

        print(f"Testing xs = {xs}")

        # Compute all prefixes
        prefixes = inits(xs)
        print(f"  Prefixes: {prefixes}")

        # Compute nonNegSum for each prefix
        nonneg_sums = [non_neg_sum(p) for p in prefixes]
        print(f"  nonNegSums: {nonneg_sums}")

        # Compute max(0, sum) for each prefix
        clamped_sums = [max(0, sum_list(p)) for p in prefixes]
        print(f"  Clamped sums: {clamped_sums}")

        # Compute maximums
        max_nonneg = max(nonneg_sums)
        max_clamped = max(clamped_sums)

        print(f"  Max nonNegSum: {max_nonneg}")
        print(f"  Max clamped sum: {max_clamped}")
        print(f"  Equal? {max_nonneg == max_clamped}")

        # Check if max nonNegSum > 0 (the H_max_pos claim)
        print(f"  Max nonNegSum > 0? {max_nonneg > 0}")

        # Find which prefixes achieve the maximum
        max_nonneg_prefixes = [p for i, p in enumerate(prefixes) if nonneg_sums[i] == max_nonneg]
        max_clamped_prefixes = [p for i, p in enumerate(prefixes) if clamped_sums[i] == max_clamped]

        print(f"  Prefixes achieving max nonNegSum: {max_nonneg_prefixes}")
        print(f"  Prefixes achieving max clamped: {max_clamped_prefixes}")
        print()

def analyze_when_max_positive():
    """Analyze when the maximum nonNegSum is positive for mixed-sign lists"""

    print("=== Analyzing when max nonNegSum > 0 for mixed-sign lists ===")
    print()

    # Test cases where mixed-sign might have max nonNegSum = 0
    problematic_cases = [
        [-1, 1],      # Simple case
        [-2, 1],      # Larger negative
        [-1, 0, 1],   # With zero
        [-3, 2],      # Even larger negative
        [-2, 1, -1],  # Negative at end
    ]

    for xs in problematic_cases:
        if not mixed_signs(xs):
            continue

        prefixes = inits(xs)
        nonneg_sums = [non_neg_sum(p) for p in prefixes]
        max_nonneg = max(nonneg_sums)

        print(f"xs = {xs}")
        print(f"  nonNegSums: {nonneg_sums}")
        print(f"  max nonNegSum: {max_nonneg}")
        print(f"  max > 0? {max_nonneg > 0}")

        if max_nonneg == 0:
            print(f"  *** COUNTEREXAMPLE: mixed-sign list with max nonNegSum = 0 ***")
        print()

def find_valid_subgoal():
    """Find what the valid computational subgoal should be"""

    print("=== Finding valid computational subgoal ===")
    print()

    print("The proof tries to establish H_max_pos: max nonNegSum > 0 for mixed-sign lists")
    print("But this is computationally false. Let's find what IS true:")
    print()

    # Test many mixed-sign cases
    mixed_cases = [
        [-1, 1], [-2, 1], [-3, 1], [-4, 1], [-5, 1],
        [1, -1], [2, -1], [3, -1], [4, -1], [5, -1],
        [-1, 0, 1], [-2, 0, 1], [1, 0, -1],
        [-1, 2], [-2, 3], [-3, 4],
        [2, -1], [3, -2], [4, -3],
        [-1, 1, -1], [-2, 1, -1], [1, -1, 1],
    ]

    max_pos_count = 0
    total_count = 0

    for xs in mixed_cases:
        if not mixed_signs(xs):
            continue

        total_count += 1
        prefixes = inits(xs)
        nonneg_sums = [non_neg_sum(p) for p in prefixes]
        max_nonneg = max(nonneg_sums)

        if max_nonneg > 0:
            max_pos_count += 1

    print(f"Out of {total_count} mixed-sign cases:")
    print(f"  {max_pos_count} have max nonNegSum > 0")
    print(f"  {total_count - max_pos_count} have max nonNegSum = 0")
    print()

    if max_pos_count == total_count:
        print("✅ The claim 'max nonNegSum > 0' holds for all tested mixed-sign cases")
        print("The proof might be correct, but needs a more sophisticated argument")
    else:
        print("❌ The claim 'max nonNegSum > 0' is FALSE for mixed-sign lists")
        print("The proof approach needs to be reconsidered")

if __name__ == "__main__":
    test_maximum_equivalence()
    analyze_when_max_positive()
    find_valid_subgoal()