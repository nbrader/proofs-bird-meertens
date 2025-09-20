#!/usr/bin/env python3

def scan_left(f, xs, init):
    """Coq's scan_left function following the recursive definition:
    scan_left f [] i = [i]
    scan_left f (x::xs') i = i :: scan_left f xs' (f i x)
    """
    if not xs:
        return [init]
    else:
        x = xs[0]
        xs_tail = xs[1:]
        return [init] + scan_left(f, xs_tail, f(init, x))

def fold_right(f, init, xs):
    """Standard fold_right implementation"""
    if not xs:
        return init
    else:
        x = xs[0]
        xs_tail = xs[1:]
        return f(x, fold_right(f, init, xs_tail))

def scan_right(f, init, xs):
    """Coq's scan_right function following the recursive definition:
    scan_right f i [] = [i]
    scan_right f i (x::xs') = let q = fold_right f i xs' in f x q :: scan_right f i xs'
    """
    if not xs:
        return [init]
    else:
        x = xs[0]
        xs_tail = xs[1:]
        q = fold_right(f, init, xs_tail)
        return [f(x, q)] + scan_right(f, init, xs_tail)

def test_scan_left_right_rev():
    """Test the equivalence: scan_left f xs init = rev(scan_right (flipped_f) init (rev xs))"""

    def nonNegPlus(a, b):
        return max(0, a + b)

    def flipped_nonNegPlus(x, acc):
        """Flipped version: f acc x becomes f x acc"""
        return nonNegPlus(acc, x)

    test_cases = [
        [],
        [1],
        [1, 2],
        [1, -2],
        [-1, 2],
        [-1, -2],
        [1, 2, 3],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -10, 3, -4, 8]
    ]

    init_values = [0, 1, -1, 5]

    for init in init_values:
        for xs in test_cases:
            print(f"Testing xs = {xs}, init = {init}")

            # Left side: scan_left f xs init
            left_result = scan_left(nonNegPlus, xs, init)

            # Right side: rev(scan_right (flipped_f) init (rev xs))
            xs_rev = list(reversed(xs))
            scan_right_result = scan_right(flipped_nonNegPlus, init, xs_rev)
            right_result = list(reversed(scan_right_result))

            print(f"  scan_left result: {left_result}")
            print(f"  scan_right on rev: {scan_right_result}")
            print(f"  rev(scan_right): {right_result}")
            print(f"  Equal: {left_result == right_result}")

            if left_result != right_result:
                print("  MISMATCH!")
                return False
            print()

    return True

if __name__ == "__main__":
    print("Testing scan_left_right_rev equivalence...")
    success = test_scan_left_right_rev()
    print(f"All tests passed: {success}")