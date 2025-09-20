#!/usr/bin/env python3

"""
Verify fold_promotion_dual conjecture:
nonNegMaximum_dual ∘ concat = nonNegMaximum_dual ∘ map nonNegMaximum_dual

Where:
- nonNegMaximum_dual = fold_left max 0
- concat = flatten list of lists
"""

def nonNegMaximum_dual(xs):
    """fold_left max xs 0"""
    result = 0
    for x in xs:
        result = max(result, x)
    return result

def concat_lists(xss):
    """Concatenate a list of lists"""
    result = []
    for xs in xss:
        result.extend(xs)
    return result

def test_fold_promotion_dual():
    """Test the fold promotion dual property"""

    # Test cases: list of lists
    test_cases = [
        [],  # empty list
        [[]],  # list with one empty list
        [[1]],  # list with one single-element list
        [[1, 2]],  # list with one multi-element list
        [[], [1]],  # empty list followed by non-empty
        [[1], []],  # non-empty followed by empty
        [[1, 2], [3, 4]],  # two non-empty lists
        [[1], [2], [3]],  # three single-element lists
        [[-1, 2], [3, -4], [5]],  # mixed positive/negative
        [[0], [0, 0], []],  # lists with zeros
        [[-5, -3], [-1], [-2, -4]],  # all negative
        [[10, -5], [3, 8], [1, 9, -2]],  # longer lists
    ]

    all_passed = True

    for i, xss in enumerate(test_cases):
        # Left side: nonNegMaximum_dual(concat(xss))
        concat_result = concat_lists(xss)
        left_side = nonNegMaximum_dual(concat_result)

        # Right side: nonNegMaximum_dual(map nonNegMaximum_dual xss)
        mapped_maxs = [nonNegMaximum_dual(xs) for xs in xss]
        right_side = nonNegMaximum_dual(mapped_maxs)

        print(f"Test {i+1}: xss = {xss}")
        print(f"  concat(xss) = {concat_result}")
        print(f"  nonNegMaximum_dual(concat(xss)) = {left_side}")
        print(f"  map nonNegMaximum_dual xss = {mapped_maxs}")
        print(f"  nonNegMaximum_dual(mapped) = {right_side}")
        print(f"  Equal? {left_side == right_side}")

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