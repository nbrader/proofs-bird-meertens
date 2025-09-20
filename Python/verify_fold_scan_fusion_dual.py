#!/usr/bin/env python3

def nonNegPlus(a, b):
    return max(0, a + b)

def scan_left(f, xs, init):
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def fold_left(f, xs, init):
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def test_fold_scan_fusion_pair_dual():
    """Test the equivalence from fold_scan_fusion_pair_dual"""

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

    for xs in test_cases:
        print(f"Testing xs = {xs}")

        # Left side: fold_left with pair function starting from (0, 0)
        def pair_func(uv, x):
            u, v = uv
            return (max(u, nonNegPlus(v, x)), nonNegPlus(v, x))

        left_result = fold_left(pair_func, xs, (0, 0))

        # Right side: tuple of separate operations
        scan_result = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, 0)
        right_u = fold_left(max, scan_result, 0)
        right_v = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, 0)
        right_result = (right_u, right_v)

        print(f"  Left:  {left_result}")
        print(f"  Right: {right_result}")
        print(f"  Equal: {left_result == right_result}")

        if left_result != right_result:
            print("  MISMATCH!")
            print(f"  Scan result: {scan_result}")
            return False
        print()

    return True

if __name__ == "__main__":
    print("Verifying fold_scan_fusion_pair_dual equivalence...")
    success = test_fold_scan_fusion_pair_dual()
    print(f"All tests passed: {success}")