#!/usr/bin/env python3
"""
Test the fold_left_transform_init helper lemma computationally.

The lemma states: f a (fold_left f xs b) = fold_left f xs (f a b)

This is a fundamental property about how operations distribute over fold_left.
"""

def fold_left(f, initial, lst):
    """Python implementation of fold_left"""
    result = initial
    for item in lst:
        result = f(result, item)
    return result

def test_fold_left_transform_init():
    """Test the transform_init property with various operations"""

    print("Testing fold_left_transform_init property")
    print("=" * 60)
    print("Property: f a (fold_left f xs b) = fold_left f xs (f a b)")
    print()

    # Test with addition (commutative and associative)
    def f_add(a, b):
        return a + b

    print("Testing with addition:")
    test_cases_add = [
        ([1, 2, 3], 5, 10),  # xs, a, b
        ([2], 3, 1),
        ([], 5, 7),
        ([1, 2, 3, 4], 0, 0),
        ([10, 20], 5, 15),
    ]

    for xs, a, b in test_cases_add:
        # LHS: f a (fold_left f xs b)
        fold_result = fold_left(f_add, b, xs)
        lhs = f_add(a, fold_result)

        # RHS: fold_left f xs (f a b)
        ab_result = f_add(a, b)
        rhs = fold_left(f_add, ab_result, xs)

        print(f"  xs={xs}, a={a}, b={b}")
        print(f"    LHS: f({a}, fold_left(f, {xs}, {b})) = f({a}, {fold_result}) = {lhs}")
        print(f"    RHS: fold_left(f, {xs}, f({a}, {b})) = fold_left(f, {xs}, {ab_result}) = {rhs}")
        print(f"    Equal: {lhs == rhs}")

        if lhs != rhs:
            print(f"    ❌ FAILED!")
            return False
        else:
            print(f"    ✅ PASSED")
        print()

    # Test with multiplication
    def f_mult(a, b):
        return a * b

    print("Testing with multiplication:")
    test_cases_mult = [
        ([2, 3], 4, 1),
        ([2], 3, 5),
        ([], 7, 11),
        ([2, 3, 4], 1, 1),
    ]

    for xs, a, b in test_cases_mult:
        fold_result = fold_left(f_mult, b, xs)
        lhs = f_mult(a, fold_result)

        ab_result = f_mult(a, b)
        rhs = fold_left(f_mult, ab_result, xs)

        print(f"  xs={xs}, a={a}, b={b}")
        print(f"    LHS: f({a}, fold_left(f, {xs}, {b})) = f({a}, {fold_result}) = {lhs}")
        print(f"    RHS: fold_left(f, {xs}, f({a}, {b})) = fold_left(f, {xs}, {ab_result}) = {rhs}")
        print(f"    Equal: {lhs == rhs}")

        if lhs != rhs:
            print(f"    ❌ FAILED!")
            return False
        else:
            print(f"    ✅ PASSED")
        print()

    # Test with max (associative, idempotent)
    def f_max(a, b):
        return max(a, b)

    print("Testing with max:")
    test_cases_max = [
        ([3, 1, 4], 2, 0),
        ([5], 3, 7),
        ([], 10, 5),
        ([1, 2, 3], 0, 4),
    ]

    for xs, a, b in test_cases_max:
        fold_result = fold_left(f_max, b, xs)
        lhs = f_max(a, fold_result)

        ab_result = f_max(a, b)
        rhs = fold_left(f_max, ab_result, xs)

        print(f"  xs={xs}, a={a}, b={b}")
        print(f"    LHS: max({a}, fold_left(max, {xs}, {b})) = max({a}, {fold_result}) = {lhs}")
        print(f"    RHS: fold_left(max, {xs}, max({a}, {b})) = fold_left(max, {xs}, {ab_result}) = {rhs}")
        print(f"    Equal: {lhs == rhs}")

        if lhs != rhs:
            print(f"    ❌ FAILED!")
            return False
        else:
            print(f"    ✅ PASSED")
        print()

    return True

def test_edge_cases():
    """Test edge cases and boundary conditions"""

    print("Testing edge cases:")
    print("=" * 30)

    def f_add(a, b):
        return a + b

    # Empty list case
    xs, a, b = [], 5, 3
    fold_result = fold_left(f_add, b, xs)
    lhs = f_add(a, fold_result)
    ab_result = f_add(a, b)
    rhs = fold_left(f_add, ab_result, xs)

    print(f"Empty list: xs={xs}, a={a}, b={b}")
    print(f"  LHS: {lhs}, RHS: {rhs}, Equal: {lhs == rhs}")

    # Single element case
    xs, a, b = [7], 2, 4
    fold_result = fold_left(f_add, b, xs)
    lhs = f_add(a, fold_result)
    ab_result = f_add(a, b)
    rhs = fold_left(f_add, ab_result, xs)

    print(f"Single element: xs={xs}, a={a}, b={b}")
    print(f"  LHS: {lhs}, RHS: {rhs}, Equal: {lhs == rhs}")

    # Zero values
    xs, a, b = [0, 0], 0, 0
    fold_result = fold_left(f_add, b, xs)
    lhs = f_add(a, fold_result)
    ab_result = f_add(a, b)
    rhs = fold_left(f_add, ab_result, xs)

    print(f"All zeros: xs={xs}, a={a}, b={b}")
    print(f"  LHS: {lhs}, RHS: {rhs}, Equal: {lhs == rhs}")

def analyze_property_algebraically():
    """Analyze why this property should hold"""

    print("\nAlgebraic Analysis:")
    print("=" * 30)
    print("The property f a (fold_left f xs b) = fold_left f xs (f a b)")
    print("should hold when f satisfies certain associativity properties.")
    print()
    print("For a list xs = [x1, x2, ..., xn]:")
    print("  fold_left f xs b = f(...f(f(b, x1), x2)..., xn)")
    print()
    print("LHS: f a (fold_left f xs b)")
    print("   = f a (f(...f(f(b, x1), x2)..., xn))")
    print()
    print("RHS: fold_left f xs (f a b)")
    print("   = f(...f(f(f(a,b), x1), x2)..., xn)")
    print()
    print("The equality requires that f can be 'distributed' through the fold.")
    print("This typically requires f to be associative or have middle associativity.")

if __name__ == "__main__":
    success = test_fold_left_transform_init()
    test_edge_cases()
    analyze_property_algebraically()

    print("\n" + "=" * 60)
    if success:
        print("✅ ALL TESTS PASSED!")
        print("The fold_left_transform_init property appears to be mathematically sound.")
        print("This supports the Coq lemma and suggests it should be provable.")
    else:
        print("❌ SOME TESTS FAILED!")
        print("The property may not hold in general or may require additional conditions.")