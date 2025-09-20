#!/usr/bin/env python3

"""
Verify the scan_left_inits_rec_fold conjecture:
scan_left f xs i = map (fun prefix => fold_left f prefix i) (inits_rec xs)
"""

def scan_left(f, xs, i):
    """scan_left f xs i accumulates f from left with initial value i"""
    if xs == []:
        return [i]
    else:
        x = xs[0]
        xs_rest = xs[1:]
        return [i] + scan_left(f, xs_rest, f(i, x))

def inits_rec(xs):
    """inits_rec returns all prefixes of xs"""
    if xs == []:
        return [[]]
    else:
        x = xs[0]
        xs_rest = xs[1:]
        return [[]] + [[x] + prefix for prefix in inits_rec(xs_rest)]

def fold_left(f, xs, i):
    """fold_left f xs i applies f from left"""
    result = i
    for x in xs:
        result = f(result, x)
    return result

def test_scan_left_inits_equivalence():
    """Test the equivalence on various examples"""

    def add(x, y):
        return x + y

    def mult(x, y):
        return x * y

    test_cases = [
        (add, [], 0),
        (add, [1], 0),
        (add, [1, 2], 0),
        (add, [1, 2, 3], 0),
        (add, [1, 2, 3, 4], 0),
        (mult, [], 1),
        (mult, [2], 1),
        (mult, [2, 3], 1),
        (mult, [2, 3, 4], 1),
        (add, [5, -2, 3], 10),
    ]

    all_passed = True

    for f, xs, i in test_cases:
        # Left side: scan_left f xs i
        left_side = scan_left(f, xs, i)

        # Right side: map (fun prefix => fold_left f prefix i) (inits_rec xs)
        inits = inits_rec(xs)
        right_side = [fold_left(f, prefix, i) for prefix in inits]

        print(f"Testing f={f.__name__}, xs={xs}, i={i}")
        print(f"  scan_left: {left_side}")
        print(f"  inits_rec: {inits}")
        print(f"  mapped: {right_side}")

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
    test_scan_left_inits_equivalence()