#!/usr/bin/env python3
"""
Test the logic for exists_nonneg_maximizing_prefix before implementing in Coq.

The lemma claims: In mixed-sign lists, if M > 0 is the maximum prefix sum,
then there exists a prefix with nonnegative sum that achieves this maximum.
"""

from typing import List

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
    has_pos = any(x > 0 for x in xs)
    has_nonpos = any(x <= 0 for x in xs)
    return has_pos and has_nonpos

def test_exists_nonneg_maximizing_prefix():
    """
    Test: For mixed-sign lists where M > 0 is max prefix sum,
    there exists a prefix with sum >= 0 that equals M.
    """

    test_cases = [
        [-1, 2, -1],      # M = 2, achieved by [−1, 2] with sum = 1 >= 0
        [-2, 3, -1],      # M = 3, achieved by [−2, 3] with sum = 1 >= 0
        [1, -2, 2],       # M = 2, achieved by [1, −2, 2] with sum = 1 >= 0
        [-1, 1, -1, 2],   # M = 2, achieved by [−1, 1, −1, 2] with sum = 1 >= 0
        [2, -3, 1],       # M = 2, achieved by [2] with sum = 2 >= 0
        [-3, 5, -1],      # M = 5, achieved by [−3, 5] with sum = 2 >= 0
    ]

    print("Testing exists_nonneg_maximizing_prefix logic")
    print("=" * 60)

    for xs in test_cases:
        if not mixed_signs(xs):
            print(f"Skipping {xs} - not mixed signs")
            continue

        prefixes = inits(xs)
        prefix_sums = [fold_right_add(p) for p in prefixes]
        M = fold_right_max(prefix_sums)

        print(f"\nInput: {xs}")
        print(f"Prefixes: {prefixes}")
        print(f"Prefix sums: {prefix_sums}")
        print(f"M = max(prefix_sums) = {M}")

        if M <= 0:
            print(f"M = {M} <= 0, lemma doesn't apply")
            continue

        # Find prefixes that achieve M and have nonnegative sum
        achieving_prefixes = []
        for i, p in enumerate(prefixes):
            p_sum = prefix_sums[i]
            if p_sum == M and p_sum >= 0:
                achieving_prefixes.append((p, p_sum))

        print(f"Prefixes achieving M = {M} with sum >= 0: {achieving_prefixes}")

        if achieving_prefixes:
            print("✅ PASS: Found nonneg prefix achieving maximum")
        else:
            print("❌ FAIL: No nonneg prefix achieves maximum")
            # This would be a counterexample to our lemma
            return xs

    print(f"\n{'=' * 60}")
    print("✅ All test cases pass - lemma logic appears sound")
    return None

def test_edge_cases():
    """Test potential edge cases"""

    print("\nTesting edge cases:")
    print("-" * 30)

    edge_cases = [
        [-1, 1],          # Minimal mixed case
        [0, 1, -1],       # Contains zero
        [-1, 0, 1],       # Zero in middle
        [1, 0, -1],       # Zero in middle, different order
    ]

    for xs in edge_cases:
        if not mixed_signs(xs):
            continue

        prefixes = inits(xs)
        prefix_sums = [sum(p) for p in prefixes]
        M = fold_right_max(prefix_sums)

        print(f"Edge case {xs}: M = {M}")

        if M > 0:
            achieving_nonneg = [(p, sum(p)) for i, p in enumerate(prefixes)
                              if prefix_sums[i] == M and prefix_sums[i] >= 0]
            print(f"  Nonneg achievers: {achieving_nonneg}")

if __name__ == "__main__":
    counterexample = test_exists_nonneg_maximizing_prefix()
    test_edge_cases()

    if counterexample:
        print(f"\n🚨 COUNTEREXAMPLE FOUND: {counterexample}")
        print("The lemma logic is false!")
    else:
        print(f"\n✅ No counterexamples found - lemma logic is sound")