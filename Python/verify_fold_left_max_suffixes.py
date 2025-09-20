#!/usr/bin/env python3

"""
Verify fold_left_nonNegPlus_eq_max_suffixes conjecture:
nonNegSum_dual xs = nonNegMaximum_dual (map nonNegSum_dual (tails xs))
"""

def nonNegPlus(x, y):
    """Non-negative addition: max(0, x + y)"""
    return max(0, x + y)

def nonNegSum_dual(xs):
    """fold_left nonNegPlus xs 0"""
    result = 0
    for x in xs:
        result = nonNegPlus(result, x)
    return result

def nonNegMaximum_dual(xs):
    """fold_left max xs 0"""
    result = 0
    for x in xs:
        result = max(result, x)
    return result

def tails(xs):
    """All suffixes of xs including empty list"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[i:])
    return result

def test_fold_left_max_suffixes():
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
        # Left side: nonNegSum_dual xs
        left_side = nonNegSum_dual(xs)

        # Right side: nonNegMaximum_dual (map nonNegSum_dual (tails xs))
        tails_xs = tails(xs)
        mapped = [nonNegSum_dual(suffix) for suffix in tails_xs]
        right_side = nonNegMaximum_dual(mapped)

        print(f"Testing xs={xs}")
        print(f"  nonNegSum_dual(xs): {left_side}")
        print(f"  tails(xs): {tails_xs}")
        print(f"  mapped sums: {mapped}")
        print(f"  nonNegMaximum_dual of mapped: {right_side}")

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
    test_fold_left_max_suffixes()