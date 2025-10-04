#!/usr/bin/env python3
"""
Computational verification of the overall lemma statement:
nonNegPlus_agrees_with_add_on_prefix : forall p, 0 <= fold_right Z.add 0 p ->
                                       fold_right nonNegPlus 0 p = fold_right Z.add 0 p.

This checks if the lemma statement itself is true by testing various lists p
where the hypothesis (0 <= sum(p)) holds and checking if the conclusion holds.
"""

def nonNegPlus(x, y):
    """Coq nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def fold_right_nonNegPlus(lst):
    """fold_right nonNegPlus 0 lst"""
    result = 0
    for val in reversed(lst):
        result = nonNegPlus(val, result)
    return result

def fold_right_add(lst):
    """fold_right Z.add 0 lst = sum(lst)"""
    return sum(lst)

def test_lemma_statement(p):
    """Test the lemma for a specific list p"""
    sum_p = fold_right_add(p)
    nonneg_sum_p = fold_right_nonNegPlus(p)

    # Check hypothesis: 0 <= sum(p)
    hypothesis_holds = (sum_p >= 0)

    # Check conclusion: nonNegSum(p) = sum(p)
    conclusion_holds = (nonneg_sum_p == sum_p)

    return hypothesis_holds, conclusion_holds

def detailed_trace_nonNegPlus(lst):
    """Show step-by-step computation of fold_right nonNegPlus"""
    print(f"Computing fold_right nonNegPlus 0 {lst}:")
    result = 0
    for i, val in enumerate(reversed(lst)):
        old_result = result
        result = nonNegPlus(val, result)
        print(f"  Step {i+1}: nonNegPlus({val}, {old_result}) = max(0, {val + old_result}) = {result}")
    return result

def comprehensive_test():
    """Test the lemma with many different lists where hypothesis holds"""
    print("COMPREHENSIVE VERIFICATION: nonNegPlus_agrees_with_add_on_prefix")
    print("="*70)
    print("Lemma statement: forall p, 0 <= sum(p) -> nonNegSum(p) = sum(p)")
    print()

    counterexamples = []
    valid_examples = []

    # Generate test cases where sum(p) >= 0
    test_cases = [
        # Basic cases
        [],
        [0],
        [1],
        [2],
        [5],

        # Positive cases
        [1, 2],
        [1, 2, 3],
        [5, 3, 2],
        [1, 1, 1, 1],

        # Mixed cases with nonnegative sum
        [2, -1],        # sum = 1
        [3, -2],        # sum = 1
        [5, -3],        # sum = 2
        [1, 2, -2],     # sum = 1
        [3, -1, -1],    # sum = 1
        [4, -2, -1],    # sum = 1
        [10, -5, -2],   # sum = 3

        # Edge case: sum = 0
        [1, -1],
        [2, -2],
        [3, -1, -2],
        [5, -2, -3],

        # Complex mixed cases
        [10, -3, -2, -1],  # sum = 4
        [8, -3, -2, -2],   # sum = 1
        [7, -2, -2, -2],   # sum = 1
        [6, -1, -2, -2],   # sum = 1
        [15, -5, -4, -3],  # sum = 3

        # Cases with negative elements at different positions
        [-1, 2],           # sum = 1
        [-2, 3],           # sum = 1
        [-1, -2, 4],       # sum = 1
        [-3, -1, 5],       # sum = 1
        [1, -1, 1],        # sum = 1
        [2, -1, -1, 2],    # sum = 2
    ]

    for p in test_cases:
        hypothesis_holds, conclusion_holds = test_lemma_statement(p)

        if hypothesis_holds:
            sum_p = fold_right_add(p)
            nonneg_sum_p = fold_right_nonNegPlus(p)

            print(f"Testing p = {p}")
            print(f"  sum(p) = {sum_p} >= 0: {hypothesis_holds}")
            print(f"  nonNegSum(p) = {nonneg_sum_p}")
            print(f"  Conclusion holds (nonNegSum(p) = sum(p)): {conclusion_holds}")

            if conclusion_holds:
                valid_examples.append(p)
                print(f"  ✓ LEMMA HOLDS")
            else:
                counterexamples.append(p)
                print(f"  ✗ COUNTEREXAMPLE FOUND!")
                print(f"    Expected: {sum_p}, Got: {nonneg_sum_p}")
                # Show detailed computation
                detailed_trace_nonNegPlus(p)
            print()

    return counterexamples, valid_examples

def analyze_counterexample():
    """Analyze a specific counterexample in detail"""
    print("="*60)
    print("DETAILED COUNTEREXAMPLE ANALYSIS")
    print("="*60)

    # A case that should fail: [2, -1]
    p = [2, -1]
    sum_p = fold_right_add(p)

    print(f"Analyzing p = {p}")
    print(f"sum(p) = {sum_p}")
    print(f"Hypothesis: 0 <= {sum_p} = {sum_p >= 0}")
    print()

    print("Expected behavior (if lemma were true):")
    print(f"  nonNegSum(p) should equal sum(p) = {sum_p}")
    print()

    print("Actual nonNegSum computation:")
    nonneg_sum_p = detailed_trace_nonNegPlus(p)
    print(f"  Final result: {nonneg_sum_p}")
    print()

    print("Analysis:")
    if nonneg_sum_p != sum_p:
        print(f"  ✗ LEMMA FAILS: {nonneg_sum_p} ≠ {sum_p}")
        print(f"  The issue: intermediate clamping changes the final result")
        print(f"  Step-by-step vs direct sum:")
        print(f"    Direct sum: 2 + (-1) = 1")
        print(f"    nonNegPlus: nonNegPlus(2, nonNegPlus(-1, 0))")
        print(f"              = nonNegPlus(2, max(0, -1))")
        print(f"              = nonNegPlus(2, 0)")
        print(f"              = max(0, 2 + 0) = 2")
        print(f"  The intermediate clamping of -1 to 0 corrupts the computation!")
    else:
        print(f"  ✓ Lemma holds for this case")

def test_mathematical_intuition():
    """Test cases that reveal the mathematical structure"""
    print("="*60)
    print("MATHEMATICAL STRUCTURE ANALYSIS")
    print("="*60)

    print("Key insight: nonNegPlus clamps intermediate results, not just the final result")
    print()

    # Cases where intermediate clamping matters
    problematic_cases = [
        ([1, -1], "Simple negative that gets clamped"),
        ([2, -1], "Positive total, but intermediate clamping affects result"),
        ([3, -2], "Same pattern, larger values"),
        ([5, -3], "Positive result, but clamping changes computation"),
        ([1, -2, 2], "Multiple negative elements"),
        ([4, -1, -2], "Negative elements at end"),
        ([-1, 3], "Negative at start"),
        ([2, -1, 1], "Interleaved positive/negative"),
    ]

    for p, description in problematic_cases:
        sum_p = fold_right_add(p)
        if sum_p >= 0:  # Only test cases where hypothesis holds
            nonneg_sum_p = fold_right_nonNegPlus(p)
            matches = (nonneg_sum_p == sum_p)

            print(f"{p}: {description}")
            print(f"  sum = {sum_p}, nonNegSum = {nonneg_sum_p}, matches = {matches}")
            if not matches:
                print(f"  ✗ COUNTEREXAMPLE")
            print()

def main():
    print("COMPUTATIONAL VERIFICATION: nonNegPlus_agrees_with_add_on_prefix")
    print("="*70)

    # First, test the mathematical intuition
    test_mathematical_intuition()

    # Then do comprehensive testing
    counterexamples, valid_examples = comprehensive_test()

    # Analyze a specific counterexample
    analyze_counterexample()

    # Final summary
    print("="*60)
    print("FINAL CONCLUSION")
    print("="*60)

    if counterexamples:
        print(f"✗ THE LEMMA IS FALSE")
        print(f"Found {len(counterexamples)} counterexample(s) where:")
        print(f"- The hypothesis holds: 0 <= sum(p)")
        print(f"- But the conclusion fails: nonNegSum(p) ≠ sum(p)")
        print()
        print("Sample counterexamples:")
        for i, p in enumerate(counterexamples[:5]):  # Show first 5
            sum_p = fold_right_add(p)
            nonneg_sum_p = fold_right_nonNegPlus(p)
            print(f"  {i+1}. p = {p}: sum = {sum_p}, nonNegSum = {nonneg_sum_p}")

        print()
        print("Root cause: The nonNegPlus operation clamps intermediate results,")
        print("not just the final result. This changes the computation even when")
        print("the final sum would be nonnegative.")
    else:
        print(f"✓ THE LEMMA APPEARS TRUE")
        print(f"All {len(valid_examples)} test cases passed.")
        print("However, this doesn't constitute a complete proof.")

    print()
    print("Mathematical insight:")
    print("The lemma fails because fold_right nonNegPlus 0 [a₁, a₂, ..., aₙ]")
    print("is NOT equivalent to max(0, a₁ + a₂ + ... + aₙ)")
    print("Instead, it's max(0, a₁ + max(0, a₂ + max(0, ...)))")
    print("The intermediate clamping operations change the result.")

if __name__ == "__main__":
    main()