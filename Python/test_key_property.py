#!/usr/bin/env python3
"""
Test the key property needed for the inductive step:

If nonNegSum(xs) = nonNegMaximum(map nonNegSum (inits xs)), then:
x <#> nonNegSum(xs) = nonNegMaximum(map (nonNegPlus x) (map nonNegSum (inits xs)))

This is the crucial distributivity property for nonNegPlus over maximum.
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

def nonNegMaximum(xs):
    """nonNegMaximum: fold_right Z.max 0 xs"""
    return fold_right(z_max, 0, xs)

def inits(xs):
    """Return all initial segments of xs, including empty list"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def test_key_distributivity(x, xs):
    """
    Test: If nonNegSum(xs) = max of prefix sums of xs, then
    x <#> nonNegSum(xs) = max(map (nonNegPlus x) (prefix sums of xs))
    """

    print(f"Testing key property for x = {x}, xs = {xs}")

    # Prerequisite: check if IH holds for xs
    sum_xs = nonNegSum(xs)
    prefix_sums = [nonNegSum(seg) for seg in inits(xs)]
    max_prefix_sums = nonNegMaximum(prefix_sums)

    print(f"  nonNegSum({xs}) = {sum_xs}")
    print(f"  prefix sums = {prefix_sums}")
    print(f"  max prefix sums = {max_prefix_sums}")
    print(f"  IH holds: {sum_xs == max_prefix_sums}")

    if sum_xs != max_prefix_sums:
        print("  Skipping - IH doesn't hold")
        return True  # Skip this test

    # Now test the key property
    lhs = nonNegPlus(x, sum_xs)
    mapped_prefix_sums = [nonNegPlus(x, s) for s in prefix_sums]
    rhs = nonNegMaximum(mapped_prefix_sums)

    print(f"  LHS: {x} <#> {sum_xs} = {lhs}")
    print(f"  map (nonNegPlus {x}) {prefix_sums} = {mapped_prefix_sums}")
    print(f"  RHS: max({mapped_prefix_sums}) = {rhs}")
    print(f"  Property holds: {lhs == rhs}")

    # Additional insight: since sum_xs = max_prefix_sums, and nonNegPlus is monotonic,
    # x <#> max_prefix_sums should equal max(map (x <#> ·) prefix_sums)

    print(f"  Key insight: {x} <#> max({prefix_sums}) = max(map ({x} <#> ·) {prefix_sums})")
    print(f"  This is the monotonicity + maximum preservation property")
    print()

    return lhs == rhs

def test_cases():
    """Test various cases"""
    test_pairs = [
        (1, []),
        (1, [2]),
        (1, [-1]),
        (-1, [2]),
        (0, [1, -1]),
        (3, [1, -2, 3]),
        (-2, [1, 2]),
        (5, [-3, 2]),
    ]

    print("Testing key distributivity property:")
    print("If nonNegSum(xs) = max(prefix_sums(xs)), then")
    print("x <#> nonNegSum(xs) = max(map (nonNegPlus x) (prefix_sums(xs)))")
    print()

    passed = 0
    failed = 0

    for x, xs in test_pairs:
        if test_key_distributivity(x, xs):
            passed += 1
        else:
            failed += 1

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("Key property verified! This suggests nonNegPlus preserves maximality.")
    else:
        print("Property failed - need to investigate further.")