#!/usr/bin/env python3

"""
Verify form7_dual_eq_form8_dual conjecture:
form7_dual = form8_dual

Where:
form7_dual xs = nonNegMaximum_dual (scan_left (fun acc x => nonNegPlus acc x) xs 0)
form8_dual xs = fst (fold_left maxSoFarAndPreviousSum_dual xs (0, 0))
"""

def nonNegPlus(x, y):
    """Non-negative addition: max(0, x + y)"""
    return max(0, x + y)

def nonNegMaximum_dual(xs):
    """fold_left max xs 0"""
    result = 0
    for x in xs:
        result = max(result, x)
    return result

def scan_left(f, xs, init):
    """Scan left function"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def fold_left(f, xs, init):
    """Fold left function"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def maxSoFarAndPreviousSum_dual(uv, x):
    """Dual version: (u, v) -> x -> (max(u, nonNegPlus(v, x)), nonNegPlus(v, x))"""
    u, v = uv
    w = nonNegPlus(v, x)
    return (max(u, w), w)

def form7_dual(xs):
    """nonNegMaximum_dual (scan_left (fun acc x => nonNegPlus acc x) xs 0)"""
    scanned = scan_left(nonNegPlus, xs, 0)
    return nonNegMaximum_dual(scanned)

def form8_dual(xs):
    """fst (fold_left maxSoFarAndPreviousSum_dual xs (0, 0))"""
    result = fold_left(maxSoFarAndPreviousSum_dual, xs, (0, 0))
    return result[0]

def test_form7_dual_eq_form8_dual():
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
        # Left side: form7_dual
        left_side = form7_dual(xs)

        # Right side: form8_dual
        right_side = form8_dual(xs)

        print(f"Testing xs={xs}")
        print(f"  form7_dual(xs): {left_side}")
        print(f"  form8_dual(xs): {right_side}")

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
    test_form7_dual_eq_form8_dual()