#!/usr/bin/env python3
"""
Test the key relationship for the proof:
fold_right nonNegPlus 0 xs = nonNegMaximum (map (fold_right nonNegPlus 0) (inits xs))

This should show whether the sum of a list equals the maximum of all prefix sums.
"""

def nonNegPlus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def z_max(x, y):
    """Z.max operation"""
    return max(x, y)

def fold_right(op, init, xs):
    """fold_right operation"""
    if not xs:
        return init
    return op(xs[0], fold_right(op, init, xs[1:]))

def nonNegMaximum(xs):
    """nonNegMaximum: fold_right Z.max 0 xs"""
    return fold_right(z_max, 0, xs)

def inits(xs):
    """Return all initial segments of xs, including empty list"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def test_key_relationship(xs):
    """Test: fold_right nonNegPlus 0 xs = nonNegMaximum (map (fold_right nonNegPlus 0) (inits xs))"""

    # LHS: direct sum
    lhs = fold_right(nonNegPlus, 0, xs)

    # RHS: maximum of prefix sums
    inits_xs = inits(xs)
    prefix_sums = [fold_right(nonNegPlus, 0, prefix) for prefix in inits_xs]
    rhs = nonNegMaximum(prefix_sums)

    print(f"xs = {xs}")
    print(f"inits(xs) = {inits_xs}")
    print(f"prefix sums = {prefix_sums}")
    print(f"LHS (direct sum) = {lhs}")
    print(f"RHS (max of prefix sums) = {rhs}")
    print(f"Equal: {lhs == rhs}")
    print()

    return lhs == rhs

def test_cases():
    """Test various cases"""
    test_lists = [
        [],
        [1],
        [-1],
        [1, 2],
        [1, -1],
        [-1, 1],
        [1, 2, 3],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -3, 2],
        [2, -5, 3, 1],
    ]

    print("Testing key relationship:")
    print("fold_right nonNegPlus 0 xs = nonNegMaximum (map (fold_right nonNegPlus 0) (inits xs))")
    print()

    passed = 0
    failed = 0

    for xs in test_lists:
        if test_key_relationship(xs):
            passed += 1
        else:
            failed += 1

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("All tests passed! The key relationship is TRUE.")
    else:
        print("Some tests failed! The key relationship is FALSE.")