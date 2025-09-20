#!/usr/bin/env python3

"""
Verify the fold_right_nonNegPlus_eq_max_prefixes conjecture:
nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))
"""

def nonNegPlus(x, y):
    """Non-negative addition: max(0, x + y)"""
    return max(0, x + y)

def nonNegSum(xs):
    """fold_right nonNegPlus 0 xs"""
    result = 0
    for x in reversed(xs):
        result = nonNegPlus(x, result)
    return result

def nonNegMaximum(xs):
    """fold_right max 0 xs"""
    result = 0
    for x in reversed(xs):
        result = max(x, result)
    return result

def inits(xs):
    """All prefixes of xs including empty list"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def test_nonNegPlus_max_prefixes():
    """Test the equivalence on various examples"""

    test_cases = [
        [],
        [0],
        [5],
        [-1],
        [1, 2],
        [-1, -2],
        [1, -2, 3],
        [-1, 2, -3],
        [1, 2, 3, 4],
        [-1, -2, -3, -4],
        [5, -3, 2, -1, 4],
        [-2, 1, -3, 4, -1, 2, 1, -5, 4],
        [1, -3, 2, 1, -1],
        [0, 0, 0],
        [10, -5, 3, -2, 8],
    ]

    all_passed = True

    for xs in test_cases:
        # Left side: nonNegSum xs
        left_side = nonNegSum(xs)

        # Right side: nonNegMaximum (map nonNegSum (inits xs))
        inits_xs = inits(xs)
        mapped = [nonNegSum(prefix) for prefix in inits_xs]
        right_side = nonNegMaximum(mapped)

        print(f"Testing xs={xs}")
        print(f"  nonNegSum(xs): {left_side}")
        print(f"  inits(xs): {inits_xs}")
        print(f"  mapped sums: {mapped}")
        print(f"  nonNegMaximum of mapped: {right_side}")

        if left_side == right_side:
            print("  ✓ PASS")
        else:
            print("  ✗ FAIL")
            all_passed = False
        print()

    if all_passed:
        print("All tests passed! The conjecture appears to be TRUE.")
    else:
        print("Some tests failed. The conjecture may be FALSE.")

    return all_passed

if __name__ == "__main__":
    test_nonNegPlus_max_prefixes()