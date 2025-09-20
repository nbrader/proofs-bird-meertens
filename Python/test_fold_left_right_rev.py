#!/usr/bin/env python3

def nonNegPlus(a, b):
    """Coq's nonNegPlus: a + b but truncated to be >= 0"""
    return max(0, a + b)

def fold_left(f, xs, init):
    """Standard fold_left implementation"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def fold_right(f, init, xs):
    """Standard fold_right implementation"""
    if not xs:
        return init
    else:
        x = xs[0]
        xs_tail = xs[1:]
        return f(x, fold_right(f, init, xs_tail))

def test_fold_left_right_rev_nonNegPlus():
    """Test fold_left (fun acc x => nonNegPlus acc x) xs init =
             fold_right (fun x acc => nonNegPlus acc x) init (rev xs)"""

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
        [5, -10, 3, -4, 8],
        [-5, 10, -3, 4, -8]
    ]

    init_values = [0, 1, 2, 5, 10]

    for init in init_values:
        for xs in test_cases:
            print(f"Testing xs = {xs}, init = {init}")

            # Left side: fold_left (fun acc x => nonNegPlus acc x) xs init
            left_result = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, init)

            # Right side: fold_right (fun x acc => nonNegPlus acc x) init (rev xs)
            xs_rev = list(reversed(xs))
            right_result = fold_right(lambda x, acc: nonNegPlus(acc, x), init, xs_rev)

            print(f"  Left:  {left_result}")
            print(f"  Right: {right_result}")
            print(f"  Equal: {left_result == right_result}")

            if left_result != right_result:
                print("  MISMATCH!")
                print(f"  xs_rev: {xs_rev}")
                return False
            print()

    return True

if __name__ == "__main__":
    print("Testing fold_left/fold_right reversal for nonNegPlus...")
    success = test_fold_left_right_rev_nonNegPlus()
    print(f"All tests passed: {success}")