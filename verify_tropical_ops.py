#!/usr/bin/env python3

def tropical_add(a, b):
    """Tropical addition = max operation"""
    if a is None:  # NegInf
        return b
    if b is None:  # NegInf
        return a
    return max(a, b)

def tropical_mul(a, b):
    """Tropical multiplication = regular addition"""
    if a is None or b is None:  # NegInf
        return None
    return a + b

def fold_right_tropical_add(xs, init=None):
    """fold_right tropical_add NegInf xs"""
    result = init
    for x in reversed(xs):
        result = tropical_add(x, result)
    return result

def fold_right_tropical_mul(xs, init=0):
    """fold_right tropical_mul (Finite 0) xs"""
    result = init
    for x in reversed(xs):
        result = tropical_mul(x, result)
        if result is None:  # Hit NegInf
            return None
    return result

def test_tropical_correspondences():
    """Test the tropical operation correspondences"""
    print("=== Testing tropical operation correspondences ===")
    print()

    # Test: fold_right tropical_mul (Finite 0) (map Finite xs) = Finite (fold_right Z.add 0 xs)
    print("Testing: fold_right tropical_mul (Finite 0) (map Finite xs) = Finite (fold_right Z.add 0 xs)")

    test_cases = [
        [],
        [1],
        [1, 2],
        [2, -1],
        [-1, 3],
        [1, -2, 3],
    ]

    for xs in test_cases:
        print(f"  xs = {xs}")

        # LHS: fold_right tropical_mul (Finite 0) (map Finite xs)
        # Since map Finite just wraps each element, we can work directly with xs
        tropical_result = fold_right_tropical_mul(xs, 0)

        # RHS: Finite (fold_right Z.add 0 xs)
        regular_sum = sum(xs)

        print(f"    tropical_mul result: {tropical_result}")
        print(f"    regular sum: {regular_sum}")
        print(f"    Equal: {tropical_result == regular_sum}")

        if tropical_result != regular_sum:
            print("    MISMATCH!")
        print()

    # Test: fold_right tropical_add NegInf (map Finite zs) = Finite (fold_right Z.max 0 zs)
    print("Testing: fold_right tropical_add NegInf (map Finite zs) = Finite (fold_right Z.max 0 zs)")

    for zs in test_cases:
        print(f"  zs = {zs}")

        # LHS: fold_right tropical_add NegInf (map Finite zs)
        tropical_result = fold_right_tropical_add(zs, None)

        # RHS: Finite (fold_right Z.max 0 zs)
        max_result = max([0] + zs) if zs else 0

        print(f"    tropical_add result: {tropical_result}")
        print(f"    max result: {max_result}")
        print(f"    Equal: {tropical_result == max_result}")

        if tropical_result != max_result:
            print("    MISMATCH!")
        print()

def test_nonNegPlus_tropical_correspondence():
    """Test: tropical_add (tropical_mul (Finite x) (Finite y)) (Finite 0) = Finite (nonNegPlus x y)"""
    print("Testing: tropical_add (tropical_mul (Finite x) (Finite y)) (Finite 0) = Finite (nonNegPlus x y)")
    print()

    def nonneg_plus(x, y):
        result = x + y
        return result if result >= 0 else 0

    test_pairs = [
        (1, 2),
        (2, -1),
        (-1, 3),
        (-2, 1),
        (0, 0),
        (5, -10),
    ]

    for x, y in test_pairs:
        print(f"  x = {x}, y = {y}")

        # LHS: tropical_add (tropical_mul (Finite x) (Finite y)) (Finite 0)
        tropical_mul_result = tropical_mul(x, y)  # x + y
        tropical_add_result = tropical_add(tropical_mul_result, 0)  # max(x + y, 0)

        # RHS: Finite (nonNegPlus x y)
        nonneg_result = nonneg_plus(x, y)

        print(f"    tropical_mul({x}, {y}) = {tropical_mul_result}")
        print(f"    tropical_add({tropical_mul_result}, 0) = {tropical_add_result}")
        print(f"    nonNegPlus({x}, {y}) = {nonneg_result}")
        print(f"    Equal: {tropical_add_result == nonneg_result}")

        if tropical_add_result != nonneg_result:
            print("    MISMATCH!")
        print()

if __name__ == "__main__":
    test_tropical_correspondences()
    test_nonNegPlus_tropical_correspondence()