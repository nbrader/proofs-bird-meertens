#!/usr/bin/env python3

"""
Verify fold_scan_fusion_pair_dual conjecture:
fold_left (fun uv x => let (u, v) = uv in (max u (nonNegPlus v x), nonNegPlus v x)) xs (0, 0)
=
(fold_left max (scan_left (fun acc x => nonNegPlus acc x) xs 0) 0,
 fold_left (fun acc x => nonNegPlus acc x) xs 0)
"""

def nonNegPlus(x, y):
    """Non-negative addition: max(0, x + y)"""
    return max(0, x + y)

def scan_left(f, xs, init):
    """Left scan: returns list of intermediate results"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def fold_left(f, xs, init):
    """Left fold"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def test_fold_scan_fusion_pair_dual():
    """Test the dual fusion property"""

    # Test cases
    test_cases = [
        [],  # empty list
        [1],  # single element
        [1, 2],  # two elements
        [-1, 2],  # mixed signs
        [3, -1, 2],  # three elements
        [0, 0, 0],  # all zeros
        [-5, -3, -1],  # all negative
        [10, -5, 3, -2],  # longer mixed list
        [1, 2, 3, 4, 5],  # all positive
        [-1, -2, -3],  # all negative
    ]

    all_passed = True

    for i, xs in enumerate(test_cases):
        # Left side: fold_left with the complex function
        def complex_f(uv, x):
            u, v = uv
            return (max(u, nonNegPlus(v, x)), nonNegPlus(v, x))

        left_side = fold_left(complex_f, xs, (0, 0))

        # Right side: pair of fold_left operations
        # First: fold_left max on scan_left results
        scan_results = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, 0)
        max_part = fold_left(max, scan_results, 0)

        # Second: fold_left nonNegPlus
        plus_part = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, 0)

        right_side = (max_part, plus_part)

        print(f"Test {i+1}: xs = {xs}")
        print(f"  Left side: {left_side}")
        print(f"  Right side: {right_side}")
        print(f"  scan_left results: {scan_results}")
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
    test_fold_scan_fusion_pair_dual()