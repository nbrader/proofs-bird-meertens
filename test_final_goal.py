#!/usr/bin/env python3
"""
Test the final goal of fold_right_nonNegPlus_eq_max_prefixes:

Given:
- xs is in inits(xs)
- for all ys in inits(xs), nonNegSum(ys) <= nonNegSum(xs)

Goal:
nonNegSum(xs) = fold_right(Z.max, 0, map(nonNegSum, inits(xs)))

This is testing whether the maximum element property holds.
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

def nonNegSum(xs):
    """nonNegSum: fold_right nonNegPlus 0 xs"""
    return fold_right(nonNegPlus, 0, xs)

def inits(xs):
    """Return all initial segments of xs, including empty list"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def test_final_goal(xs):
    """
    Test the final goal:
    nonNegSum(xs) = fold_right(Z.max, 0, map(nonNegSum, inits(xs)))
    """
    print(f"Testing final goal for xs = {xs}")

    # Check preconditions
    inits_xs = inits(xs)
    print(f"  inits(xs) = {inits_xs}")

    # Check that xs is in inits(xs)
    xs_in_inits = xs in inits_xs
    print(f"  xs in inits(xs): {xs_in_inits}")

    # Check that xs achieves maximum nonNegSum
    nonNegSums = [nonNegSum(seg) for seg in inits_xs]
    print(f"  nonNegSums = {nonNegSums}")

    xs_sum = nonNegSum(xs)
    max_nonNegSum = max(nonNegSums)
    xs_achieves_max = xs_sum == max_nonNegSum
    print(f"  nonNegSum(xs) = {xs_sum}")
    print(f"  max(nonNegSums) = {max_nonNegSum}")
    print(f"  xs achieves maximum: {xs_achieves_max}")

    # Test the goal
    lhs = xs_sum
    rhs = fold_right(z_max, 0, nonNegSums)

    print(f"  LHS: nonNegSum(xs) = {lhs}")
    print(f"  RHS: fold_right(Z.max, 0, nonNegSums) = fold_right(Z.max, 0, {nonNegSums}) = {rhs}")
    print(f"  Goal holds: {lhs == rhs}")

    # Key insight: if xs achieves the maximum value in the list,
    # then fold_right Z.max should return that maximum value
    expected_rhs = max_nonNegSum if nonNegSums else 0
    print(f"  Expected RHS (max of list): {expected_rhs}")
    print(f"  RHS matches expected: {rhs == expected_rhs}")
    print()

    return lhs == rhs

def test_fold_right_max_property():
    """Test that fold_right Z.max returns the maximum element"""
    test_lists = [
        [],
        [0],
        [5],
        [1, 3, 2],
        [0, 5, 2, 1],
        [3, 1, 4, 1, 5],
    ]

    print("Testing fold_right Z.max property:")
    for lst in test_lists:
        fold_result = fold_right(z_max, 0, lst)
        expected = max(lst) if lst else 0
        print(f"  fold_right(Z.max, 0, {lst}) = {fold_result}, max = {expected}, equal: {fold_result == expected}")
    print()

def test_cases():
    """Test various cases"""
    test_lists = [
        [],
        [1],
        [0],
        [-1],
        [1, 2],
        [1, -1],
        [-1, 1],
        [1, 2, 3],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -3, 2],
    ]

    print("Testing final goal of fold_right_nonNegPlus_eq_max_prefixes:")
    print("nonNegSum(xs) = fold_right(Z.max, 0, map(nonNegSum, inits(xs)))")
    print()

    # First test the fold_right Z.max property
    test_fold_right_max_property()

    passed = 0
    failed = 0

    for xs in test_lists:
        if test_final_goal(xs):
            passed += 1
        else:
            failed += 1

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("Final goal verified! The property holds.")
    else:
        print("Final goal failed - need to investigate.")