#!/usr/bin/env python3
"""
Find the exact problematic case mentioned in the Coq proof:
We need x + nonNegSum(xs') < 0 but x + sum(xs') > 0
"""

def nonNegPlus(a, b):
    return max(0, a + b)

def nonNegSum(xs):
    result = 0
    for x in xs:
        result = nonNegPlus(x, result)
    return result

def regular_sum(xs):
    return sum(xs)

def find_problematic_case():
    """Try to construct a case where x + nonNegSum(xs') < 0 but x + sum(xs') > 0"""

    print("Searching for problematic case...")
    print("Need: x + nonNegSum(xs') < 0 AND x + sum(xs') > 0")
    print("This means: nonNegSum(xs') - sum(xs') < x < -sum(xs')")
    print()

    found = False

    # Try various combinations
    for x in range(-10, 1):  # x should be negative or zero to make x + nonNegSum < 0 possible
        for tail_length in range(1, 4):
            # Generate tail lists that could cause the discrepancy
            for tail in [[-5, -2], [-3, -4], [-1, -6], [-2, -2, -2], [-8], [-10, 3]]:
                if len(tail) != tail_length:
                    continue

                xs_tail = tail
                nns_tail = nonNegSum(xs_tail)
                rs_tail = regular_sum(xs_tail)

                clamping_condition = x + nns_tail < 0
                positive_sum_condition = x + rs_tail > 0

                if clamping_condition and positive_sum_condition:
                    print(f"FOUND PROBLEMATIC CASE!")
                    print(f"x = {x}, xs' = {xs_tail}")
                    print(f"nonNegSum(xs') = {nns_tail}")
                    print(f"sum(xs') = {rs_tail}")
                    print(f"x + nonNegSum(xs') = {x + nns_tail} < 0 ✓")
                    print(f"x + sum(xs') = {x + rs_tail} > 0 ✓")
                    print(f"Difference: nonNegSum(xs') - sum(xs') = {nns_tail - rs_tail}")
                    print()
                    found = True

    if not found:
        print("No problematic case found!")
        print()
        print("This suggests that the condition might be impossible.")
        print("Let's prove why...")
        print()

        print("THEORETICAL ANALYSIS:")
        print("We know that nonNegSum(xs') >= sum(xs') when sum(xs') >= 0")
        print("And nonNegSum(xs') >= 0 always")
        print()
        print("Case 1: sum(xs') >= 0")
        print("  Then nonNegSum(xs') >= sum(xs') >= 0")
        print("  If x + sum(xs') > 0, then x > -sum(xs') >= -nonNegSum(xs')")
        print("  So x + nonNegSum(xs') >= x + sum(xs') > 0, contradicting x + nonNegSum(xs') < 0")
        print()
        print("Case 2: sum(xs') < 0")
        print("  Then for x + sum(xs') > 0, we need x > -sum(xs') > 0")
        print("  Since x > 0 and nonNegSum(xs') >= 0, we have x + nonNegSum(xs') > 0")
        print("  This contradicts x + nonNegSum(xs') < 0")
        print()
        print("Therefore, the problematic case is impossible!")

find_problematic_case()

# Additional verification: prove nonNegSum >= sum when sum >= 0
print("\n" + "="*60)
print("VERIFICATION OF KEY LEMMA:")
print("nonNegSum(xs) >= sum(xs) when sum(xs) >= 0")
print("="*60)

def verify_lemma(xs):
    nns = nonNegSum(xs)
    rs = regular_sum(xs)
    if rs >= 0:
        print(f"xs = {xs}: sum = {rs}, nonNegSum = {nns}, nonNegSum >= sum: {nns >= rs}")
        return nns >= rs
    return True

test_cases = [
    [1, 2, 3],
    [0, 0, 0],
    [5, -2, -1],  # sum = 2 >= 0
    [-1, 3, 4],   # sum = 6 >= 0
    [2, -1, -1],  # sum = 0 >= 0
    [-2, 3, 1],   # sum = 2 >= 0
]

all_pass = True
for xs in test_cases:
    if not verify_lemma(xs):
        all_pass = False

print(f"\nAll cases pass: {all_pass}")