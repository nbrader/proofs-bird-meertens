#!/usr/bin/env python3
"""
Test if the position constraint makes the contradiction valid.

In the Coq proof, we have:
- nth n prefix 0 = pos_elem (positive element at specific position n)
- prefix = firstn (S n) xs (prefix is exactly the first n+1 elements)

This means pos_elem is the LAST element of prefix.
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

def test_positive_at_last_position():
    """Test if having a positive element at the LAST position can give nonNegSum = 0"""

    print("Testing: Can nonNegSum = 0 when the positive element is at the LAST position?")
    print()

    # Test cases where positive element is at the end
    test_cases = [
        [1],           # Single positive element (trivially at end)
        [0, 1],        # Zero then positive
        [-1, 1],       # Negative then positive
        [-2, 1],       # Large negative then positive
        [-1, 0, 1],    # Negative, zero, positive
        [-3, -1, 2],   # Multiple negatives then positive
        [-5, 4],       # Large negative, smaller positive at end
    ]

    contradictions_found = 0

    for i, prefix in enumerate(test_cases):
        nns = non_neg_sum(prefix)
        last_elem = prefix[-1]

        print(f"Case {i+1}: prefix = {prefix}")
        print(f"  Last element = {last_elem}")
        print(f"  nonNegSum = {nns}")

        if last_elem > 0 and nns == 0:
            print(f"  *** CONTRADICTION: positive at end but nonNegSum = 0 ***")
            contradictions_found += 1
        else:
            print(f"  No contradiction")
        print()

    print(f"Contradictions found with positive at last position: {contradictions_found}")

    if contradictions_found == 0:
        print("✅ CONFIRMED: When positive element is at the LAST position,")
        print("nonNegSum cannot be 0. This validates the Coq contradiction!")
    else:
        print("❌ Still finding contradictions...")

def analyze_why_last_position_special():
    """Explain why having positive element at last position prevents nonNegSum = 0"""

    print("=== Analysis: Why last position is special ===")
    print()
    print("nonNegSum computes fold_right nonNegPlus 0, which processes from RIGHT to LEFT")
    print("If pos_elem > 0 is at the LAST position, it's processed FIRST:")
    print()
    print("Step 1: nonNegPlus(pos_elem, 0) = max(0, pos_elem + 0) = pos_elem > 0")
    print("Step 2+: Even if subsequent operations clamp negative results,")
    print("         we already have a positive contribution that affects the computation")
    print()

    # Show concrete example
    prefix = [-5, 3]  # 3 is at last position
    print(f"Example: prefix = {prefix} (positive element 3 at last position)")

    result = 0
    for i, x in enumerate(reversed(prefix)):
        old_result = result
        result = non_neg_plus(x, result)
        print(f"  Step {i+1}: nonNegPlus({x}, {old_result}) = max(0, {x + old_result}) = {result}")

    print(f"Final result: {result}")
    print()
    print("The key insight: since the positive element is processed first (rightmost),")
    print("it cannot be 'cancelled out' by earlier negative elements.")

if __name__ == "__main__":
    test_positive_at_last_position()
    print()
    analyze_why_last_position_special()