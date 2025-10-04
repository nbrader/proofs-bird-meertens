#!/usr/bin/env python3
"""
Analyze the exact constraint from the Coq proof.

Key hypotheses:
- prefix := firstn (S n) xs  (prefix is first n+1 elements of xs)
- nth n xs 0 = pos_elem      (element at position n in xs is positive)
- nth n prefix 0 = pos_elem  (element at position n in prefix is positive)
- n < length xs              (n is valid index)

This means:
- prefix has exactly n+1 elements
- pos_elem is at position n in both xs and prefix
- pos_elem is the LAST element of prefix (since prefix has n+1 elements, indices 0..n)
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

def firstn(n, lst):
    """Take first n elements of list"""
    return lst[:n]

def test_exact_constraint():
    """Test the exact constraint from Coq proof"""

    print("Testing exact Coq constraint:")
    print("- prefix = firstn(n+1, xs)")
    print("- pos_elem at position n in both xs and prefix")
    print("- pos_elem > 0")
    print("- nonNegSum(prefix) = 0")
    print()

    # Test various scenarios
    test_cases = [
        # (xs, n, description)
        ([1], 0, "Single positive element"),
        ([-1, 1], 1, "Negative then positive"),
        ([-2, 1], 1, "Large negative then positive"),
        ([-1, 0, 1], 2, "Negative, zero, positive"),
        ([-3, -1, 2], 2, "Multiple negatives then positive"),
        ([0, -1, 1], 2, "Zero, negative, positive"),
        ([-5, -2, 3], 2, "Multiple large negatives then positive"),
    ]

    contradictions = 0

    for xs, n, desc in test_cases:
        if n >= len(xs):
            continue

        prefix = firstn(n + 1, xs)
        pos_elem = xs[n]
        nns = non_neg_sum(prefix)

        print(f"Case: {desc}")
        print(f"  xs = {xs}")
        print(f"  n = {n}")
        print(f"  prefix = firstn({n+1}, xs) = {prefix}")
        print(f"  pos_elem = xs[{n}] = {pos_elem}")
        print(f"  nonNegSum(prefix) = {nns}")

        if pos_elem > 0 and nns == 0:
            print(f"  *** CONTRADICTION CONFIRMED ***")
            contradictions += 1
        else:
            print(f"  No contradiction (as expected)")
        print()

    print(f"Total contradictions found: {contradictions}")
    print()

    if contradictions > 0:
        print("❌ The constraint doesn't prevent the contradiction!")
        print("This suggests the Coq proof goal might be unprovable with just these hypotheses.")
    else:
        print("✅ No contradictions found - the constraint seems to prevent impossible cases.")

def analyze_mixed_signs_constraint():
    """Check if the mixed_signs constraint provides additional information"""

    print("=== Additional Analysis: mixed_signs constraint ===")
    print("The Coq proof has 'mixed_signs xs' which means:")
    print("- NOT all elements are non-negative")
    print("- NOT all elements are non-positive")
    print("- Therefore xs contains BOTH positive and negative elements")
    print()
    print("However, this doesn't directly constrain the prefix structure...")
    print()

if __name__ == "__main__":
    test_exact_constraint()
    analyze_mixed_signs_constraint()

    print("=== Conclusion ===")
    print("The computational analysis shows that the Coq goal 'False' may not be")
    print("directly provable from the given hypotheses alone. The proof likely needs")
    print("additional structural properties or a more sophisticated argument about")
    print("how positive elements in mixed-sign lists contribute to nonNegSum.")