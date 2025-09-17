#!/usr/bin/env python3
"""
Test the key property needed to complete fold_right_nonNegPlus_eq_max_prefixes:

We need to show that fold_right Z.max 0 returns the maximum element when:
1. The maximum element is in the list
2. All other elements are <= that maximum

This is essentially showing that fold_right Z.max finds the maximum of a list.
"""

def z_max(x, y):
    """Z.max operation"""
    return max(x, y)

def fold_right(op, init, xs):
    """fold_right operation"""
    if not xs:
        return init
    return op(xs[0], fold_right(op, init, xs[1:]))

def nonNegPlus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def nonNegSum(xs):
    """nonNegSum: fold_right nonNegPlus 0 xs"""
    return fold_right(nonNegPlus, 0, xs)

def inits(xs):
    """Return all initial segments of xs, including empty list"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def test_fold_right_max_property(xs, expected_max, max_in_list):
    """
    Test: If expected_max is in xs and all elements in xs are <= expected_max,
    then fold_right Z.max 0 xs = expected_max
    """
    result = fold_right(z_max, 0, xs)
    actual_max = max(xs) if xs else 0

    print(f"  xs = {xs}")
    print(f"  expected_max = {expected_max}")
    print(f"  max_in_list = {max_in_list}")
    print(f"  fold_right(Z.max, 0, xs) = {result}")
    print(f"  actual max(xs) = {actual_max}")
    print(f"  result == expected_max: {result == expected_max}")

    return result == expected_max

def test_main_goal(xs):
    """Test the main goal: nonNegSum xs = fold_right Z.max 0 (map nonNegSum (inits xs))"""

    print(f"\nTesting main goal for xs = {xs}")

    # Check preconditions
    inits_xs = inits(xs)
    prefix_sums = [nonNegSum(seg) for seg in inits_xs]

    print(f"  inits(xs) = {inits_xs}")
    print(f"  prefix_sums = {prefix_sums}")

    # Check that xs is in inits(xs)
    xs_in_inits = xs in inits_xs
    print(f"  xs in inits(xs): {xs_in_inits}")

    # Check that nonNegSum(xs) is max of prefix sums
    xs_sum = nonNegSum(xs)
    max_prefix = max(prefix_sums) if prefix_sums else 0

    print(f"  nonNegSum(xs) = {xs_sum}")
    print(f"  max(prefix_sums) = {max_prefix}")
    print(f"  xs achieves max: {xs_sum == max_prefix}")

    # Test our fold_right property
    fold_result = fold_right(z_max, 0, prefix_sums)
    print(f"  fold_right(Z.max, 0, prefix_sums) = {fold_result}")

    # The main goal
    goal_holds = xs_sum == fold_result
    print(f"  GOAL: {xs_sum} == {fold_result} : {goal_holds}")

    # Additional analysis: all prefix sums <= xs_sum?
    all_le = all(s <= xs_sum for s in prefix_sums)
    print(f"  All prefix sums <= nonNegSum(xs): {all_le}")

    return goal_holds

def test_fold_right_max_examples():
    """Test specific examples of fold_right Z.max behavior"""

    examples = [
        [],
        [0],
        [5],
        [1, 3, 2],
        [0, 5, 2, 1],
        [3, 1, 4, 1, 5],
        [0, 0, 0],
        [7, 2, 7, 3], # duplicate max
    ]

    print("Testing fold_right Z.max property:")
    print("Should return max(xs) for non-empty xs, 0 for empty xs")
    print()

    all_pass = True

    for xs in examples:
        expected = max(xs) if xs else 0
        result = fold_right(z_max, 0, xs)
        passes = result == expected

        print(f"fold_right(Z.max, 0, {xs}) = {result}, expected = {expected}, pass = {passes}")

        if not passes:
            all_pass = False

    print(f"\nAll examples pass: {all_pass}")
    return all_pass

def test_main_examples():
    """Test the main goal on various examples"""

    examples = [
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

    print("\nTesting main goal: nonNegSum(xs) = fold_right(Z.max, 0, map(nonNegSum, inits(xs)))")
    print()

    all_pass = True

    for xs in examples:
        passes = test_main_goal(xs)
        if not passes:
            all_pass = False
        print()

    print(f"All main goal tests pass: {all_pass}")
    return all_pass

if __name__ == "__main__":
    print("=== Testing fold_right Z.max property ===")
    fold_max_pass = test_fold_right_max_examples()

    print("\n=== Testing main goal ===")
    main_goal_pass = test_main_examples()

    print(f"\nSummary:")
    print(f"fold_right Z.max works correctly: {fold_max_pass}")
    print(f"Main goal holds: {main_goal_pass}")

    if fold_max_pass and main_goal_pass:
        print("\nConclusion: The property is computationally verified!")
        print("fold_right Z.max does indeed return the maximum element.")
        print("We can proceed with completing the Coq proof.")
    else:
        print("\nSome tests failed - need to investigate further.")