#!/usr/bin/env python3

def nonNegPlus(a, b):
    """Coq's nonNegPlus: a + b but truncated to be >= 0"""
    return max(0, a + b)

def scan_left(f, xs, init):
    """Coq's scan_left function following the recursive definition"""
    if not xs:
        return [init]
    else:
        x = xs[0]
        xs_tail = xs[1:]
        return [init] + scan_left(f, xs_tail, f(init, x))

def fold_left(f, xs, init):
    """Standard fold_left implementation"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def test_fold_scan_fusion_general():
    """Test the general equivalence from fold_scan_fusion_pair_general"""

    def pair_func(uv, x):
        u, v = uv
        v_new = nonNegPlus(v, x)
        u_new = max(u, v_new)
        return (u_new, v_new)

    # Test cases with various initial values that satisfy the hypotheses
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

    # Test with different initial values that satisfy: u0 >= v0 and v0 >= 0
    init_cases = [
        (0, 0),    # u0 = 0, v0 = 0
        (5, 0),    # u0 = 5, v0 = 0
        (5, 3),    # u0 = 5, v0 = 3
        (10, 5),   # u0 = 10, v0 = 5
        (1, 1),    # u0 = 1, v0 = 1
        (20, 15),  # u0 = 20, v0 = 15
    ]

    for u0, v0 in init_cases:
        assert u0 >= v0 and v0 >= 0, f"Invalid initial values: u0={u0}, v0={v0}"

        for xs in test_cases:
            print(f"Testing xs = {xs}, u0 = {u0}, v0 = {v0}")

            # Left side: fold_left with pair function starting from (u0, v0)
            left_result = fold_left(pair_func, xs, (u0, v0))

            # Right side: tuple of separate operations
            scan_result = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, v0)
            right_u = fold_left(max, scan_result, u0)
            right_v = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, v0)
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

def test_edge_cases():
    """Test additional edge cases and boundary conditions"""

    def pair_func(uv, x):
        u, v = uv
        v_new = nonNegPlus(v, x)
        u_new = max(u, v_new)
        return (u_new, v_new)

    # Edge cases with larger ranges
    import random

    print("Testing random cases...")
    for _ in range(100):
        # Generate random list
        xs = [random.randint(-10, 15) for _ in range(random.randint(0, 8))]

        # Generate random initial values satisfying constraints
        v0 = random.randint(0, 10)  # v0 >= 0
        u0 = random.randint(v0, v0 + 10)  # u0 >= v0

        # Left side
        left_result = fold_left(pair_func, xs, (u0, v0))

        # Right side
        scan_result = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, v0)
        right_u = fold_left(max, scan_result, u0)
        right_v = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, v0)
        right_result = (right_u, right_v)

        if left_result != right_result:
            print(f"RANDOM CASE FAILURE:")
            print(f"  xs = {xs}, u0 = {u0}, v0 = {v0}")
            print(f"  Left:  {left_result}")
            print(f"  Right: {right_result}")
            print(f"  Scan:  {scan_result}")
            return False

    print("All random tests passed!")
    return True

if __name__ == "__main__":
    print("Verifying fold_scan_fusion_pair_general equivalence...")
    success1 = test_fold_scan_fusion_general()
    print(f"Main tests passed: {success1}")

    if success1:
        success2 = test_edge_cases()
        print(f"Edge case tests passed: {success2}")
        print(f"Overall success: {success1 and success2}")
    else:
        print("Main tests failed, skipping edge cases")