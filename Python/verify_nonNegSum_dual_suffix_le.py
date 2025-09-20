#!/usr/bin/env python3

"""
Verify nonNegSum_dual_suffix_le conjecture:
(exists zs, zs ++ xs = ys) -> nonNegSum_dual xs <= nonNegSum_dual ys

In other words: if xs is a suffix of ys, then nonNegSum_dual xs <= nonNegSum_dual ys
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

def test_nonNegSum_dual_suffix_le():
    """Test the suffix monotonicity property"""

    # Test cases: (prefix, suffix) pairs where prefix + suffix = full list
    test_cases = [
        ([], []),
        ([], [1]),
        ([], [-1]),
        ([1], [2]),
        ([1, 2], [3]),
        ([-1], [2, 3]),
        ([1, -2], [3, 4]),
        ([-1, -2], [1, 2]),
        ([5, -3], [2, -1, 4]),
        ([-2, 1], [-3, 4, -1, 2, 1, -5, 4]),
        ([1, -3], [2, 1, -1]),
        ([0], [0, 0]),
        ([10, -5], [3, -2, 8]),
        ([1, 2, 3], []),  # suffix is empty
    ]

    all_passed = True

    for prefix, suffix in test_cases:
        full_list = prefix + suffix

        # Test: nonNegSum_dual(suffix) <= nonNegSum_dual(full_list)
        left_side = nonNegSum_dual(suffix)
        right_side = nonNegSum_dual(full_list)

        print(f"Testing prefix={prefix}, suffix={suffix}")
        print(f"  full_list={full_list}")
        print(f"  nonNegSum_dual(suffix): {left_side}")
        print(f"  nonNegSum_dual(full_list): {right_side}")
        print(f"  suffix <= full? {left_side <= right_side}")

        if left_side <= right_side:
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
    test_nonNegSum_dual_suffix_le()