#!/usr/bin/env python3
"""
Verify the key insight for maximum_equivalence_in_mixed_case:
In mixed cases, the maximum subarray sum is >= 0, so nonNegPlus behaves like regular addition
for the subarray that achieves the maximum.
"""

def nonneg_plus(x, y):
    """Simulate nonNegPlus: max(0, x + y)"""
    return max(0, x + y)

def fold_right_nonneg_plus(xs, acc=0):
    """fold_right nonNegPlus 0"""
    result = acc
    for x in reversed(xs):
        result = nonneg_plus(x, result)
    return result

def fold_right_add(xs, acc=0):
    """fold_right Z.add 0"""
    return sum(xs) + acc

def inits(xs):
    """Generate all initial segments of xs"""
    return [xs[:i] for i in range(len(xs) + 1)]

def maximum_with_base(values, base=0):
    """max(base, max(values)) if values is non-empty, else base"""
    if not values:
        return base
    return max(base, max(values))

def is_mixed_signs(xs):
    """Check if xs has both positive and non-positive elements (mixed signs)"""
    if not xs:
        return False
    has_nonneg = any(x >= 0 for x in xs)
    has_nonpos = any(x <= 0 for x in xs)
    return has_nonneg and has_nonpos and not (all(x >= 0 for x in xs) or all(x <= 0 for x in xs))

def test_maximum_equivalence(xs):
    """
    Test if maximum_equivalence_in_mixed_case holds for mixed-signs list xs
    """
    if not is_mixed_signs(xs):
        return None, "Not mixed signs"

    # Left side: maximum of nonNegPlus version
    nonneg_sums = [fold_right_nonneg_plus(prefix) for prefix in inits(xs)]
    max_nonneg = maximum_with_base(nonneg_sums, 0)

    # Right side: maximum of regular addition version
    regular_sums = [fold_right_add(prefix) for prefix in inits(xs)]
    max_regular = maximum_with_base(regular_sums, 0)

    # Key insight: In mixed cases, max_regular should be >= 0
    max_regular_nonneg = max_regular >= 0

    equal = (max_nonneg == max_regular)

    return {
        'xs': xs,
        'nonneg_sums': nonneg_sums,
        'regular_sums': regular_sums,
        'max_nonneg': max_nonneg,
        'max_regular': max_regular,
        'max_regular_nonneg': max_regular_nonneg,
        'equal': equal
    }

# Test cases
test_cases = [
    [-2, 3, -1, 4],  # Mixed: has both pos and neg, max should be at [3] or [-2,3,-1,4]
    [1, -2, 3, -1],  # Mixed: max should be at [1] or [3] or [1,-2,3]
    [-1, 2, -3, 4, -2],  # Mixed
    [2, -1, -2, 3],  # Mixed
    [-3, 1, 4, -2, -1, 2],  # Mixed
]

print("Testing maximum_equivalence_in_mixed_case...")
print("="*60)

for i, xs in enumerate(test_cases):
    result = test_maximum_equivalence(xs)
    if result is None:
        continue

    print(f"Test {i+1}: {xs}")
    print(f"  nonNegPlus sums: {result['nonneg_sums']}")
    print(f"  regular sums:    {result['regular_sums']}")
    print(f"  Max nonNegPlus: {result['max_nonneg']}")
    print(f"  Max regular:    {result['max_regular']} (>= 0: {result['max_regular_nonneg']})")
    print(f"  Equal: {result['equal']}")

    # Show where the maximum is achieved
    regular_max_idx = result['regular_sums'].index(result['max_regular'])
    print(f"  Max achieved at prefix: {inits(xs)[regular_max_idx]}")
    print()

# Key insight verification
print("KEY INSIGHT VERIFICATION:")
print("In mixed-sign cases, the maximum subarray sum should be >= 0")
print("because we can always choose a non-empty subarray with positive contribution.")
print("When the maximum sum is >= 0, nonNegPlus behaves exactly like regular addition.")