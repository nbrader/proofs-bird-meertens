#!/usr/bin/env python3
"""
Analyze whether we actually need the nonNegPlus_agrees_with_add_on_prefix lemma
in its current form, and explore alternative formulations that could be useful.
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

def analyze_usage_context():
    """Analyze the context where this lemma is used in the broader proof"""
    print("USAGE CONTEXT ANALYSIS")
    print("="*50)

    print("The lemma appears in maximum_equivalence_in_mixed_case where we need:")
    print("  fold_right nonNegPlus 0 p = fold_right Z.add 0 p")
    print("  for some prefix p where fold_right Z.add 0 p >= 0")
    print()

    print("Key insight: We're dealing with PREFIXES that achieve the MAXIMUM")
    print("In the mixed case, the maximum subarray sum is >= 0")
    print("So we're only applying this to prefixes that:")
    print("1. Have nonnegative sum")
    print("2. Achieve the maximum among all prefixes")
    print()

def test_maximum_achieving_prefixes():
    """Test the lemma specifically on prefixes that achieve the maximum"""
    print("TESTING ON MAXIMUM-ACHIEVING PREFIXES")
    print("="*50)

    # Simulate some mixed-sign lists and their prefix sums
    test_cases = [
        # Format: (list, description)
        ([3, -1, 2], "Mixed with positive maximum"),
        ([5, -2, -1], "Large positive start"),
        ([2, -3, 4], "Dip then recover"),
        ([1, 1, -1, 2], "Multiple elements"),
        ([4, -2, -1, 3], "Complex pattern"),
    ]

    for lst, description in test_cases:
        print(f"\nTesting: {lst} ({description})")

        # Compute all prefix sums (both regular and nonNegPlus)
        prefixes = []
        for i in range(len(lst) + 1):
            prefix = lst[:i]
            regular_sum = fold_right_add(prefix)
            nonneg_sum = fold_right_nonNegPlus(prefix)
            prefixes.append((prefix, regular_sum, nonneg_sum))

        # Find the maximum regular sum and which prefixes achieve it
        max_regular = max(regular_sum for _, regular_sum, _ in prefixes)
        maximizing_prefixes = [
            (prefix, regular_sum, nonneg_sum)
            for prefix, regular_sum, nonneg_sum in prefixes
            if regular_sum == max_regular
        ]

        print(f"  All prefixes and their sums:")
        for prefix, regular_sum, nonneg_sum in prefixes:
            marker = " MAX" if regular_sum == max_regular else ""
            agreement = "✓" if regular_sum == nonneg_sum else "✗"
            print(f"    {prefix}: regular={regular_sum}, nonNeg={nonneg_sum} {agreement}{marker}")

        print(f"  Maximum regular sum: {max_regular}")
        print(f"  Maximizing prefixes: {len(maximizing_prefixes)}")

        # Check if lemma holds for maximizing prefixes
        for prefix, regular_sum, nonneg_sum in maximizing_prefixes:
            if regular_sum >= 0:  # Only check when hypothesis holds
                agrees = (regular_sum == nonneg_sum)
                print(f"    {prefix}: lemma holds = {agrees}")

def explore_alternative_formulations():
    """Explore alternative formulations that might be more useful"""
    print("\n" + "="*60)
    print("ALTERNATIVE FORMULATION ANALYSIS")
    print("="*60)

    print("Current (false) lemma:")
    print("  forall p, 0 <= sum(p) -> nonNegSum(p) = sum(p)")
    print()

    print("ALTERNATIVE 1: Strengthened hypothesis")
    print("  forall p, (0 <= sum(p) AND all_prefixes_nonnegative(p)) -> nonNegSum(p) = sum(p)")
    print()

    print("ALTERNATIVE 2: Inequality version")
    print("  forall p, 0 <= sum(p) -> sum(p) <= nonNegSum(p)")
    print("  (This is always true and might be sufficient)")
    print()

    print("ALTERNATIVE 3: Conditional equality")
    print("  forall p, (0 <= sum(p) AND nonNegSum(p) = sum(p)) -> property_holds")
    print("  (Use the cases where they happen to agree)")
    print()

    print("ALTERNATIVE 4: Maximum-specific version")
    print("  forall p, (p achieves maximum AND sum(p) >= 0) -> nonNegSum(p) = sum(p)")
    print("  (More restrictive but might be provable for our specific use case)")

def test_all_prefixes_nonnegative():
    """Test Alternative 1: strengthened hypothesis"""
    print("\nTESTING ALTERNATIVE 1: Strengthened hypothesis")
    print("-" * 50)

    def all_prefixes_nonnegative(lst):
        """Check if all prefixes have nonnegative sum"""
        cumsum = 0
        for val in lst:
            cumsum += val
            if cumsum < 0:
                return False
        return True

    # Test cases where all prefixes are nonnegative
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [2, -1, 3],  # All prefix sums: 0, 2, 1, 4 (all >= 0)
        [3, -1, 2],  # All prefix sums: 0, 3, 2, 4 (all >= 0)
        [5, -2, 1],  # All prefix sums: 0, 5, 3, 4 (all >= 0)
    ]

    print("Testing: all_prefixes_nonnegative(p) -> nonNegSum(p) = sum(p)")

    for lst in test_cases:
        sum_p = fold_right_add(lst)
        nonneg_sum_p = fold_right_nonNegPlus(lst)
        all_prefixes_ok = all_prefixes_nonnegative(lst)

        if all_prefixes_ok and sum_p >= 0:
            agrees = (sum_p == nonneg_sum_p)
            print(f"  {lst}: sum={sum_p}, nonNegSum={nonneg_sum_p}, agrees={agrees}")

            if not agrees:
                print(f"    ✗ COUNTEREXAMPLE to Alternative 1!")

def test_inequality_version():
    """Test Alternative 2: inequality version"""
    print("\nTESTING ALTERNATIVE 2: Inequality version")
    print("-" * 50)

    print("Testing: 0 <= sum(p) -> sum(p) <= nonNegSum(p)")

    # This should always be true due to the nature of nonNegPlus
    test_cases = [
        [1, -1],
        [2, -1],
        [3, -2],
        [1, 2, -2],
        [5, -3],
        [10, -5, -2],
        [-1, 2],
        [-2, 3],
        [1, -1, 1],
    ]

    counterexamples = 0
    for lst in test_cases:
        sum_p = fold_right_add(lst)
        nonneg_sum_p = fold_right_nonNegPlus(lst)

        if sum_p >= 0:  # Hypothesis
            inequality_holds = (sum_p <= nonneg_sum_p)
            print(f"  {lst}: {sum_p} <= {nonneg_sum_p} = {inequality_holds}")

            if not inequality_holds:
                counterexamples += 1
                print(f"    ✗ COUNTEREXAMPLE!")

    if counterexamples == 0:
        print("  ✓ INEQUALITY VERSION APPEARS ALWAYS TRUE!")
        print("  This could be the replacement we need.")

def analyze_what_we_actually_need():
    """Analyze what property we actually need for the broader proof"""
    print("\n" + "="*60)
    print("WHAT DO WE ACTUALLY NEED?")
    print("="*60)

    print("In the broader proof context (maximum_equivalence_in_mixed_case):")
    print()
    print("We're trying to show:")
    print("  fold_right Z.max 0 (map nonNegSum (inits xs)) =")
    print("  fold_right Z.max 0 (map sum (inits xs))")
    print()
    print("The key insight:")
    print("1. There exists a prefix p that achieves max(map sum (inits xs))")
    print("2. This maximum is >= 0 (in mixed case)")
    print("3. We need to show the maxima are equal")
    print()
    print("SUFFICIENT CONDITIONS:")
    print("A. If nonNegSum(p) >= sum(p) for all p (Alternative 2)")
    print("   AND there exists some p* where nonNegSum(p*) = sum(p*)")
    print("   AND p* achieves the maximum")
    print("   THEN the maxima are equal")
    print()
    print("B. We don't need the lemma for ALL prefixes")
    print("   We only need it for the specific maximizing prefix(es)")
    print()
    print("This suggests we should:")
    print("1. Use the inequality version as a general property")
    print("2. Prove existence of agreeing maximizing prefixes specifically")
    print("3. Avoid the false general equality lemma")

def main():
    analyze_usage_context()
    test_maximum_achieving_prefixes()
    explore_alternative_formulations()
    test_all_prefixes_nonnegative()
    test_inequality_version()
    analyze_what_we_actually_need()

    print("\n" + "="*60)
    print("FINAL RECOMMENDATION")
    print("="*60)
    print("❌ DON'T use the current false lemma")
    print("✅ DO use Alternative 2: inequality version")
    print("✅ DO prove existence of specific agreeing cases")
    print("✅ DO restructure the proof to avoid the false equality")
    print()
    print("The inequality sum(p) <= nonNegSum(p) when sum(p) >= 0")
    print("appears to always hold and may be sufficient for the broader proof.")

if __name__ == "__main__":
    main()