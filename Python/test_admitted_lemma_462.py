#!/usr/bin/env python3
"""
Test script for the exact admitted lemma at line 462 in Lemmas.v:

Lemma generalised_horners_rule'_applied : forall xs : list Z,
  nonNegMaximum (map (fun x : list Z => nonNegMaximum (map nonNegSum (inits x))) (tails_rec xs)) =
  nonNegMaximum (map (fold_right nonNegPlus 0) (tails_rec xs)).

This tests the core equivalence:
  nonNegMaximum (map nonNegSum (inits ys)) = fold_right nonNegPlus 0 ys

Where:
- nonNegSum is fold_left nonNegPlus 0 (left fold)
- nonNegPlus is max(0, x + y)
- inits returns all initial segments of a list
- fold_right is Haskell-style right fold
- tails_rec is the recursive definition of tails
"""

import random
import sys

def non_neg_plus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def non_neg_sum_left(lst):
    """nonNegSum using fold_left (standard Python iteration)"""
    result = 0
    for x in lst:
        result = non_neg_plus(x, result)
    return result

def non_neg_sum_right(lst):
    """nonNegSum using fold_right (Haskell-style foldr)"""
    if not lst:
        return 0
    return non_neg_plus(lst[0], non_neg_sum_right(lst[1:]))

def non_neg_maximum(lst):
    """nonNegMaximum: maximum of a list (handles empty case)"""
    if not lst:
        return 0  # Handle empty list case
    return max(lst)

def inits(lst):
    """All initial segments of a list"""
    return [lst[:i] for i in range(len(lst) + 1)]

def tails_rec(lst):
    """Recursive definition of tails (as used in Coq)"""
    return [lst[i:] for i in range(len(lst) + 1)]

def left_side_462(ys):
    """
    Left side for a single tail ys: nonNegMaximum (map nonNegSum (inits ys))

    This computes the maximum of all prefix sums of ys using left fold.
    """
    initial_segments = inits(ys)
    sums = [non_neg_sum_left(init) for init in initial_segments]
    return non_neg_maximum(sums)

def right_side_462(ys):
    """
    Right side for a single tail ys: fold_right nonNegPlus 0 ys

    This computes the total sum of ys using right fold.
    """
    return non_neg_sum_right(ys)

def test_core_equivalence_462(ys):
    """Test the core equivalence for a single list ys"""
    left = left_side_462(ys)
    right = right_side_462(ys)
    return left == right, (left, right)

def full_lemma_462(xs):
    """
    Test the full lemma 462 for a complete list xs:
    nonNegMaximum (map (fun x => nonNegMaximum (map nonNegSum (inits x))) (tails_rec xs)) =
    nonNegMaximum (map (fold_right nonNegPlus 0) (tails_rec xs))
    """
    tails_list = tails_rec(xs)

    # Left side: apply nonNegMaximum ∘ map nonNegSum ∘ inits to each tail
    left_components = [left_side_462(tail) for tail in tails_list]
    left_result = non_neg_maximum(left_components)

    # Right side: apply fold_right nonNegPlus 0 to each tail
    right_components = [right_side_462(tail) for tail in tails_list]
    right_result = non_neg_maximum(right_components)

    return left_result == right_result, (left_result, right_result, left_components, right_components)

def detailed_analysis_462(lst):
    """Show detailed step-by-step analysis for lemma 462"""
    print(f"\nDetailed analysis for lemma 462 with {lst}:")
    print("=" * 60)

    print(f"Testing core equivalence for individual lists:")
    print(f"  nonNegMaximum (map nonNegSum (inits ys)) ?= fold_right nonNegPlus 0 ys")
    print()

    # Test core equivalence on the input list itself
    left_core, right_core = test_core_equivalence_462(lst)[1]
    core_equal = left_core == right_core
    print(f"Core test on {lst}:")
    print(f"  Left (max of prefix sums):  {left_core}")
    print(f"  Right (total sum):          {right_core}")
    print(f"  Core equivalence holds?     {core_equal}")

    if not core_equal:
        # Show the detailed computation
        print(f"\n  Detailed core computation:")
        initial_segments = inits(lst)
        print(f"    inits({lst}) = {initial_segments}")
        sums = [non_neg_sum_left(init) for init in initial_segments]
        print(f"    map nonNegSum = {sums}")
        print(f"    maximum = {max(sums) if sums else 0}")
        print(f"    fold_right nonNegPlus 0 {lst} = {non_neg_sum_right(lst)}")

    print()

    # Test full lemma
    print(f"Testing full lemma 462:")
    tails_list = tails_rec(lst)
    print(f"  tails_rec({lst}) = {tails_list}")

    left_components = []
    right_components = []

    print(f"\n  Component-wise analysis:")
    for i, tail in enumerate(tails_list):
        left_comp = left_side_462(tail)
        right_comp = right_side_462(tail)
        left_components.append(left_comp)
        right_components.append(right_comp)
        comp_equal = left_comp == right_comp
        status = "✓" if comp_equal else "✗"
        print(f"    {status} tail[{i}] = {tail}")
        print(f"       Left (max prefix sums):  {left_comp}")
        print(f"       Right (total sum):       {right_comp}")
        print(f"       Equal: {comp_equal}")

    print(f"\n  Final computation:")
    left_result = non_neg_maximum(left_components)
    right_result = non_neg_maximum(right_components)
    print(f"    Left components:  {left_components}")
    print(f"    Right components: {right_components}")
    print(f"    nonNegMaximum(left):  {left_result}")
    print(f"    nonNegMaximum(right): {right_result}")
    print(f"    Full lemma holds? {left_result == right_result}")

    return left_result == right_result

def main():
    print("Testing Admitted Lemma at Line 462 from Lemmas.v")
    print("=" * 70)
    print("Core equivalence: nonNegMaximum (map nonNegSum (inits ys)) = fold_right nonNegPlus 0 ys")
    print("Full lemma: Applied to all tails of a list")
    print("=" * 70)

    # Test cases including problematic ones
    test_cases = [
        [],                    # Empty list
        [1],                   # Single positive
        [-1],                  # Single negative
        [0],                   # Single zero
        [1, 2],                # Two positive
        [-1, -2],              # Two negative
        [1, -1],               # Mixed
        [-3, 1, 1],            # The alleged counterexample
        [1, -2, 3],            # Classic example
        [0, 1],                # Simple case
        [1, 1],                # Two positive same
        [2, 0],                # Ends with zero
        [1, 2, 3],             # All positive
        [-1, -2, -3],          # All negative
        [5, -3, -2],           # Starts positive, ends negative
        [-5, 3, 2],            # Starts negative, ends positive
        [1, -2, 3, -1, 2],     # Longer mixed
        [10, -5, 3, -2, 1],    # Another longer case
        [0, 1, 0, -1, 2],      # With zeros
        [2, -3, 4, -1, 2, 1, -5, 4]  # Complex case
    ]

    print("\nTesting CORE EQUIVALENCE on individual lists:")
    print("-" * 50)

    core_counterexamples = []

    for lst in test_cases:
        equal, (left, right) = test_core_equivalence_462(lst)
        status = "✓" if equal else "✗"
        print(f"{status} {str(lst):25} => L={left:3}, R={right:3}, equal={equal}")

        if not equal:
            core_counterexamples.append((lst, left, right))

    print(f"\nCore equivalence summary:")
    print(f"  Test cases: {len(test_cases)}")
    print(f"  Core failures: {len(core_counterexamples)}")

    print("\nTesting FULL LEMMA 462:")
    print("-" * 50)

    full_counterexamples = []

    for lst in test_cases:
        equal, (left, right, left_comp, right_comp) = full_lemma_462(lst)
        status = "✓" if equal else "✗"
        print(f"{status} {str(lst):25} => L={left:3}, R={right:3}, equal={equal}")

        if not equal:
            full_counterexamples.append((lst, left, right))

    print(f"\nFull lemma summary:")
    print(f"  Test cases: {len(test_cases)}")
    print(f"  Full failures: {len(full_counterexamples)}")

    if core_counterexamples:
        print(f"\n❌ CORE EQUIVALENCE FAILS for {len(core_counterexamples)} cases:")
        for lst, left, right in core_counterexamples[:5]:
            print(f"  {lst}: max_prefix_sums={left}, total_sum={right}")

    if full_counterexamples:
        print(f"\n❌ FULL LEMMA 462 FAILS for {len(full_counterexamples)} cases:")
        for lst, left, right in full_counterexamples[:5]:
            print(f"  {lst}: L={left}, R={right}")

    if not core_counterexamples and not full_counterexamples:
        print("\n✅ Both core equivalence and full lemma 462 HOLD for all test cases!")

    # Detailed analysis of key cases
    print("\n" + "=" * 70)
    print("DETAILED ANALYSIS OF KEY CASES:")
    print("=" * 70)

    key_cases = [
        [-3, 1, 1],           # The alleged counterexample
        [1, -2, 3],           # Classic case
        [0, 1],               # Simple case
        []                    # Empty case
    ]

    for lst in key_cases:
        detailed_analysis_462(lst)

    # Random testing
    print("\n" + "=" * 70)
    print("RANDOM TESTING:")
    print("=" * 70)

    core_random_failures = []
    full_random_failures = []
    num_random_tests = 500

    print(f"Running {num_random_tests} random tests...")

    for i in range(num_random_tests):
        # Generate random list
        length = random.randint(0, 8)  # Smaller lists for tails computation
        lst = [random.randint(-10, 10) for _ in range(length)]

        # Test core equivalence
        core_equal, _ = test_core_equivalence_462(lst)
        if not core_equal:
            core_random_failures.append(lst)

        # Test full lemma
        full_equal, _ = full_lemma_462(lst)
        if not full_equal:
            full_random_failures.append(lst)

        if (i + 1) % 100 == 0:
            print(f"  Progress: {i + 1}/{num_random_tests}, core failures: {len(core_random_failures)}, full failures: {len(full_random_failures)}")

    print(f"\nRandom test results:")
    print(f"  Tests run: {num_random_tests}")
    print(f"  Core failures: {len(core_random_failures)}")
    print(f"  Full failures: {len(full_random_failures)}")

    # Final conclusion
    total_core_failures = len(core_counterexamples) + len(core_random_failures)
    total_full_failures = len(full_counterexamples) + len(full_random_failures)
    total_tests = len(test_cases) + num_random_tests

    print("\n" + "=" * 70)
    print("FINAL CONCLUSION:")
    print("=" * 70)

    if total_core_failures == 0:
        print("🎉 Core equivalence holds for all tests!")
        print("   nonNegMaximum (map nonNegSum (inits ys)) = fold_right nonNegPlus 0 ys")
    else:
        print(f"❌ Core equivalence FAILS ({total_core_failures}/{total_tests} cases)")
        print("   This is the fundamental issue blocking the proof.")

    if total_full_failures == 0:
        print("🎉 Full lemma 462 holds for all tests!")
        print("   The admitted lemma appears to be TRUE and provable.")
    else:
        print(f"❌ Full lemma 462 FAILS ({total_full_failures}/{total_tests} cases)")
        print("   The admitted lemma is FALSE and needs correction.")

if __name__ == "__main__":
    # Set random seed for reproducibility if provided
    if len(sys.argv) > 1:
        seed = int(sys.argv[1])
        random.seed(seed)
        print(f"Using random seed: {seed}")

    main()