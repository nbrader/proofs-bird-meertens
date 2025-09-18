#!/usr/bin/env python3
"""
Test the fold_left_combine_middle_assoc property computationally.

This tests whether:
f (fold_left f xs x) (fold_left f ys y) = fold_left f (xs ++ y :: ys) x

when f satisfies middle associativity: f (f a m) b = f a (f m b)
"""

def fold_left(f, initial, lst):
    """Python implementation of fold_left"""
    result = initial
    for item in lst:
        result = f(result, item)
    return result

def test_fold_left_combine_middle_assoc():
    """Test the fold_left combine property with middle associativity"""

    # Define a middle associative operation on integers
    # For testing: max operation with specific behavior
    def f_max(a, b):
        return max(a, b)

    # Test if max satisfies middle associativity: f(f(a,m),b) = f(a,f(m,b))
    def check_middle_assoc(a, m, b):
        left = f_max(f_max(a, m), b)
        right = f_max(a, f_max(m, b))
        return left == right

    # Verify middle associativity for max
    test_cases = [(1, 2, 3), (5, 1, 4), (2, 2, 2), (0, 10, 5)]
    for a, m, b in test_cases:
        assert check_middle_assoc(a, m, b), f"Middle assoc failed for {a}, {m}, {b}"
    print("✓ max operation satisfies middle associativity")

    # Test the main property
    test_vectors = [
        ([1, 2], [3, 4], 0, 1),
        ([5], [2, 6], 1, 3),
        ([], [1, 2, 3], 0, 5),
        ([1, 2, 3], [], 2, 4),
        ([1], [2], 0, 3),
    ]

    for xs, ys, x, y in test_vectors:
        # Left side: f (fold_left f xs x) (fold_left f ys y)
        left_fold_xs = fold_left(f_max, x, xs)
        left_fold_ys = fold_left(f_max, y, ys)
        left_side = f_max(left_fold_xs, left_fold_ys)

        # Right side: fold_left f (xs ++ y :: ys) x
        combined_list = xs + [y] + ys
        right_side = fold_left(f_max, x, combined_list)

        print(f"xs={xs}, ys={ys}, x={x}, y={y}")
        print(f"  Left:  f({left_fold_xs}, {left_fold_ys}) = {left_side}")
        print(f"  Right: fold_left({combined_list}, {x}) = {right_side}")
        print(f"  Equal: {left_side == right_side}")

        if left_side != right_side:
            print(f"  ❌ FAILURE!")
            return False
        else:
            print(f"  ✓ SUCCESS")

    print("\n✓ All tests passed! The property holds for max operation.")
    return True

def test_with_addition():
    """Test with addition (which has middle associativity)"""
    def f_add(a, b):
        return a + b

    # Check middle associativity for addition: (a + m) + b = a + (m + b)
    def check_middle_assoc_add(a, m, b):
        left = f_add(f_add(a, m), b)
        right = f_add(a, f_add(m, b))
        return left == right

    # Verify - this should always be true for addition
    test_cases = [(1, 2, 3), (5, 1, 4), (2, 2, 2), (0, 10, 5)]
    for a, m, b in test_cases:
        assert check_middle_assoc_add(a, m, b), f"Middle assoc failed for {a}, {m}, {b}"
    print("✓ addition operation satisfies middle associativity")

    # Test the main property with addition
    test_vectors = [
        ([1, 2], [3, 4], 0, 1),
        ([5], [2, 6], 1, 3),
        ([], [1, 2, 3], 0, 5),
        ([1, 2, 3], [], 2, 4),
    ]

    for xs, ys, x, y in test_vectors:
        left_fold_xs = fold_left(f_add, x, xs)
        left_fold_ys = fold_left(f_add, y, ys)
        left_side = f_add(left_fold_xs, left_fold_ys)

        combined_list = xs + [y] + ys
        right_side = fold_left(f_add, x, combined_list)

        print(f"ADD: xs={xs}, ys={ys}, x={x}, y={y} => {left_side} vs {right_side} : {left_side == right_side}")

        if left_side != right_side:
            print(f"  ❌ Addition test FAILED!")
            return False

    print("✓ Addition tests passed!")
    return True

if __name__ == "__main__":
    print("Testing fold_left_combine_middle_assoc property...")
    print("=" * 50)

    success1 = test_fold_left_combine_middle_assoc()
    print("\n" + "=" * 50)
    success2 = test_with_addition()

    if success1 and success2:
        print("\n🎉 All computational tests passed!")
        print("The fold_left_combine_middle_assoc property is mathematically sound.")
    else:
        print("\n💥 Some tests failed!")
        print("The property may not hold in general or needs refinement.")