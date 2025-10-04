#!/usr/bin/env python3
"""
Verify the relationship between nonNegSum and regular sum
to understand the complex case in the Coq proof.
"""

def nonNegPlus(a, b):
    """Non-negative plus: returns max(0, a + b)"""
    return max(0, a + b)

def nonNegSum(xs):
    """Compute nonNegSum using fold_left"""
    result = 0
    for x in xs:
        result = nonNegPlus(x, result)
    return result

def regular_sum(xs):
    """Regular sum"""
    return sum(xs)

def test_relationship(xs, description=""):
    """Test the relationship for a specific list"""
    nns = nonNegSum(xs)
    rs = regular_sum(xs)
    print(f"\n{description}")
    print(f"List: {xs}")
    print(f"nonNegSum: {nns}")
    print(f"Regular sum: {rs}")
    print(f"nonNegSum >= regular_sum: {nns >= rs}")

    # Test the problematic case from the proof
    if len(xs) > 0:
        x = xs[0]
        xs_tail = xs[1:]
        nns_tail = nonNegSum(xs_tail)
        rs_tail = regular_sum(xs_tail)

        clamping_condition = x + nns_tail < 0
        sum_nonneg = rs >= 0

        print(f"First element x: {x}")
        print(f"nonNegSum tail: {nns_tail}")
        print(f"Regular sum tail: {rs_tail}")
        print(f"x + nonNegSum_tail: {x + nns_tail}")
        print(f"x + regular_sum_tail: {x + rs_tail}")
        print(f"Clamping occurs (x + nonNegSum_tail < 0): {clamping_condition}")
        print(f"Regular sum non-negative: {sum_nonneg}")

        # The problematic case: clamping occurs but regular sum is positive
        if clamping_condition and x + rs_tail > 0:
            print("*** PROBLEMATIC CASE: clamping but positive regular sum ***")
            print(f"This means nonNegSum_tail < regular_sum_tail by: {rs_tail - nns_tail}")

# Test cases
test_cases = [
    ([1, 2, 3], "All positive"),
    ([-1, -2, -3], "All negative"),
    ([0, 0, 0], "All zero"),
    ([5, -3, -1], "Mixed: positive first"),
    ([-5, 3, 4], "Mixed: negative first, positive sum"),
    ([-10, 5, 2], "Mixed: negative first, negative sum"),
    ([3, -8, 2], "Complex case"),
    ([-1, -2, 5], "Case that might trigger the problem"),
    ([2, -5, 1, 3], "Longer mixed case"),
]

for xs, desc in test_cases:
    test_relationship(xs, desc)

print("\n" + "="*50)
print("ANALYSIS OF THE PROBLEMATIC CASE")
print("="*50)

# The key insight: let's construct a case where the problem occurs
# We need: x + nonNegSum(xs') < 0 but x + sum(xs') > 0
# This means: nonNegSum(xs') < sum(xs')

# This can happen when xs' has negative elements that cause clamping in nonNegSum
# but the final sum is still negative overall

xs_problematic = [-2, -3, 8]  # sum = 3 > 0, but nonNegSum will clamp
x = xs_problematic[0]
xs_tail = xs_problematic[1:]

print(f"\nConstructed problematic case:")
test_relationship(xs_problematic, "Constructed problematic case")

# Let's trace through nonNegSum step by step
print(f"\nStep-by-step nonNegSum calculation for {xs_problematic}:")
result = 0
for i, val in enumerate(xs_problematic):
    old_result = result
    result = nonNegPlus(val, result)
    print(f"Step {i+1}: {val} + {old_result} -> nonNegPlus({val}, {old_result}) = {result}")