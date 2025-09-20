#!/usr/bin/env python3

"""
Verify the Original_Dual_Equivalence conjecture:
form1 = form1_dual
"""

def max_seg_sum_orig(xs):
    """Original form1: maximum segment sum"""
    if not xs:
        return 0

    max_sum = 0
    for i in range(len(xs)):
        for j in range(i + 1, len(xs) + 1):
            segment = xs[i:j]
            seg_sum = max(0, sum(segment))
            max_sum = max(max_sum, seg_sum)
    return max_sum

def max_seg_sum_dual(xs):
    """Dual form1: left-to-right computation"""
    if not xs:
        return 0

    max_ending_here = 0
    max_so_far = 0

    for x in xs:
        max_ending_here = max(0, max_ending_here + x)
        max_so_far = max(max_so_far, max_ending_here)

    return max_so_far

def test_form1_dual_equivalence():
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
        orig_result = max_seg_sum_orig(xs)
        dual_result = max_seg_sum_dual(xs)

        print(f"Testing xs={xs}")
        print(f"  form1 (original): {orig_result}")
        print(f"  form1_dual: {dual_result}")

        if orig_result == dual_result:
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
    test_form1_dual_equivalence()