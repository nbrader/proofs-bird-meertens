#!/usr/bin/env python3
"""
Test script for the exact admitted lemma at line 447 in Lemmas.v:

Lemma generalised_horners_rule :
  fold_right (fun x y => x <|> y) 0 ∘ map (fold_right (fun x y => x <#> y) 0) ∘ inits =
  fold_right (fun x y => (x <#> y) <|> 0) 0.

Where:
- <#> is nonNegPlus: max(0, x + y)
- <|> is Z.max: max(x, y)
- inits returns all initial segments of a list
- fold_right is Haskell-style right fold
"""

import random
import sys

def non_neg_plus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def z_max(x, y):
    """Z.max operation: max(x, y)"""
    return max(x, y)

def fold_right(op, initial, lst):
    """Haskell-style fold_right (foldr)"""
    if not lst:
        return initial
    return op(lst[0], fold_right(op, initial, lst[1:]))

def inits(lst):
    """All initial segments of a list"""
    return [lst[:i] for i in range(len(lst) + 1)]

def left_side_447(lst):
    """
    Left side: fold_right (fun x y => x <|> y) 0 ∘ map (fold_right (fun x y => x <#> y) 0) ∘ inits

    Step by step:
    1. inits lst -> get all initial segments
    2. map (fold_right (fun x y => x <#> y) 0) -> fold each segment with nonNegPlus
    3. fold_right (fun x y => x <|> y) 0 -> fold the results with z_max
    """
    # Step 1: Get all initial segments
    initial_segments = inits(lst)

    # Step 2: Apply fold_right nonNegPlus 0 to each segment
    folded_segments = [fold_right(non_neg_plus, 0, seg) for seg in initial_segments]

    # Step 3: Apply fold_right z_max 0 to the results
    result = fold_right(z_max, 0, folded_segments)

    return result

def right_side_447(lst):
    """
    Right side: fold_right (fun x y => (x <#> y) <|> 0) 0

    This is a single fold with a compound operation:
    For each element x and accumulator y, compute (x <#> y) <|> 0
    """
    def compound_op(x, y):
        # (x <#> y) <|> 0 = max(max(0, x + y), 0) = max(0, x + y) = nonNegPlus(x, y)
        return z_max(non_neg_plus(x, y), 0)

    return fold_right(compound_op, 0, lst)

def test_lemma_447(lst):
    """Test if the lemma at line 447 holds for a given list"""
    left = left_side_447(lst)
    right = right_side_447(lst)
    return left == right, (left, right)

def detailed_analysis_447(lst):
    """Show detailed step-by-step analysis for lemma 447"""
    print(f"\nDetailed analysis for lemma 447 with {lst}:")
    print("=" * 60)

    # Left side computation
    print("LEFT SIDE:")
    initial_segments = inits(lst)
    print(f"  inits({lst}) = {initial_segments}")

    folded_segments = []
    for i, seg in enumerate(initial_segments):
        folded = fold_right(non_neg_plus, 0, seg)
        folded_segments.append(folded)
        print(f"  fold_right nonNegPlus 0 {seg} = {folded}")

    print(f"  Folded segments: {folded_segments}")
    left_result = fold_right(z_max, 0, folded_segments)
    print(f"  fold_right z_max 0 {folded_segments} = {left_result}")

    # Right side computation
    print("\nRIGHT SIDE:")
    print(f"  fold_right compound_op 0 {lst}")

    # Show step-by-step right fold computation
    def show_right_fold(lst, acc=0, depth=0):
        indent = "  " * (depth + 1)
        if not lst:
            print(f"{indent}Base case: {acc}")
            return acc
        x = lst[0]
        rest = lst[1:]
        print(f"{indent}compound_op({x}, fold_right(compound_op, 0, {rest}))")
        rest_result = show_right_fold(rest, acc, depth + 1)
        result = z_max(non_neg_plus(x, rest_result), 0)
        print(f"{indent}= z_max(non_neg_plus({x}, {rest_result}), 0)")
        print(f"{indent}= z_max({non_neg_plus(x, rest_result)}, 0) = {result}")
        return result

    right_result = show_right_fold(lst)

    print(f"\nRESULT:")
    print(f"  Left side:  {left_result}")
    print(f"  Right side: {right_result}")
    print(f"  Equal? {left_result == right_result}")

    return left_result == right_result, (left_result, right_result)

def main():
    print("Testing Admitted Lemma at Line 447 from Lemmas.v")
    print("=" * 70)
    print("Testing: fold_right (x <|> y) 0 ∘ map (fold_right (x <#> y) 0) ∘ inits")
    print("       = fold_right ((x <#> y) <|> 0) 0")
    print("Where <#> = nonNegPlus, <|> = z_max")
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

    counterexamples = []

    print("\nTesting specific cases:")
    print("-" * 40)

    for i, lst in enumerate(test_cases):
        equal, (left, right) = test_lemma_447(lst)
        status = "✓" if equal else "✗"
        print(f"{status} {str(lst):25} => L={left:3}, R={right:3}, equal={equal}")

        if not equal:
            counterexamples.append((lst, left, right))

    print(f"\nSummary:")
    print(f"Total test cases: {len(test_cases)}")
    print(f"Counterexamples found: {len(counterexamples)}")

    if counterexamples:
        print(f"\n❌ Lemma 447 FAILS for {len(counterexamples)} cases:")
        for lst, left, right in counterexamples[:5]:  # Show first 5
            print(f"  {lst}: L={left}, R={right}")
        if len(counterexamples) > 5:
            print(f"  ... and {len(counterexamples) - 5} more cases")
    else:
        print("✅ Lemma 447 HOLDS for all test cases!")

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
        detailed_analysis_447(lst)

    # Random testing
    print("\n" + "=" * 70)
    print("RANDOM TESTING:")
    print("=" * 70)

    random_failures = []
    num_random_tests = 500

    print(f"Running {num_random_tests} random tests...")

    for i in range(num_random_tests):
        # Generate random list
        length = random.randint(0, 10)
        lst = [random.randint(-20, 20) for _ in range(length)]

        equal, (left, right) = test_lemma_447(lst)

        if not equal:
            random_failures.append((lst, left, right))

        if (i + 1) % 100 == 0:
            print(f"  Progress: {i + 1}/{num_random_tests}, {len(random_failures)} failures so far")

    print(f"\nRandom test results:")
    print(f"  Tests run: {num_random_tests}")
    print(f"  Failures: {len(random_failures)}")

    if random_failures:
        print(f"  First few random counterexamples:")
        for lst, left, right in random_failures[:3]:
            print(f"    {lst}: L={left}, R={right}")

    # Final conclusion
    total_failures = len(counterexamples) + len(random_failures)
    total_tests = len(test_cases) + num_random_tests

    print("\n" + "=" * 70)
    print("FINAL CONCLUSION:")
    print("=" * 70)

    if total_failures == 0:
        print("🎉 All tests passed! Lemma 447 appears to be TRUE.")
        print("\nThis means the admitted lemma can likely be proven.")
    else:
        print(f"❌ Found {total_failures} counterexamples out of {total_tests} total tests.")
        print("Lemma 447 is FALSE and should not be admitted without proof.")
        print("\nThis confirms the lemma needs correction or alternative approach.")

if __name__ == "__main__":
    # Set random seed for reproducibility if provided
    if len(sys.argv) > 1:
        seed = int(sys.argv[1])
        random.seed(seed)
        print(f"Using random seed: {seed}")

    main()