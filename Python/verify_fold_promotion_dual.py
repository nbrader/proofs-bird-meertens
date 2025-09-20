#!/usr/bin/env python3

"""
Verify the fold_promotion_dual conjecture:
nonNegMaximum_dual ∘ concat = nonNegMaximum_dual ∘ map nonNegMaximum_dual
"""

def nonNegMaximum_dual(xs):
    """fold_left Z.max xs 0"""
    result = 0
    for x in xs:
        result = max(result, x)
    return result

def concat(xss):
    """Concatenate list of lists"""
    result = []
    for xs in xss:
        result.extend(xs)
    return result

def test_fold_promotion_dual():
    """Test the equivalence on various examples"""

    test_cases = [
        [],
        [[]],
        [[1]],
        [[1, 2]],
        [[], [3]],
        [[1], [2]],
        [[1, 2], [3, 4]],
        [[1, 2, 3], [4, 5], [6]],
        [[0, -1], [2, -3], [4]],
        [[-5, -2], [-1, -4]],
        [[1], [], [2], []],
    ]

    all_passed = True

    for xss in test_cases:
        # Left side: nonNegMaximum_dual(concat(xss))
        left_side = nonNegMaximum_dual(concat(xss))

        # Right side: nonNegMaximum_dual(map(nonNegMaximum_dual, xss))
        mapped = [nonNegMaximum_dual(xs) for xs in xss]
        right_side = nonNegMaximum_dual(mapped)

        print(f"Testing xss={xss}")
        print(f"  concat: {concat(xss)}")
        print(f"  left_side (max of concat): {left_side}")
        print(f"  mapped: {mapped}")
        print(f"  right_side (max of mapped): {right_side}")

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
    test_fold_promotion_dual()