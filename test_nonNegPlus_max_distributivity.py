#!/usr/bin/env python3
"""
Test the key distributivity property of nonNegPlus over maximum:
x <#> max(ys) = max(map (nonNegPlus x) ys)

This is the fundamental property needed for the inductive proof.
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

def test_distributivity(x, ys):
    """Test: x <#> max(ys) = max(map (nonNegPlus x) ys)"""

    if not ys:
        # Edge case: empty list
        max_ys = 0  # max of empty list is 0 for nonNegMaximum
        lhs = nonNegPlus(x, max_ys)
        rhs = 0  # max of empty mapped list is 0
        result = lhs == rhs
        print(f"x = {x}, ys = [] (empty)")
        print(f"  LHS: {x} <#> max([]) = {x} <#> 0 = {lhs}")
        print(f"  RHS: max(map ({x} <#> ·) []) = max([]) = {rhs}")
        print(f"  Equal: {result}")
        return result

    max_ys = nonNegMaximum(ys)
    lhs = nonNegPlus(x, max_ys)

    mapped = [nonNegPlus(x, y) for y in ys]
    rhs = nonNegMaximum(mapped)

    result = lhs == rhs

    print(f"x = {x}, ys = {ys}")
    print(f"  max(ys) = {max_ys}")
    print(f"  LHS: {x} <#> {max_ys} = {lhs}")
    print(f"  map ({x} <#> ·) {ys} = {mapped}")
    print(f"  RHS: max({mapped}) = {rhs}")
    print(f"  Equal: {result}")

    # Additional analysis
    if not result:
        print(f"  FAILURE ANALYSIS:")
        for i, (y, mapped_val) in enumerate(zip(ys, mapped)):
            print(f"    ys[{i}] = {y}, {x} <#> {y} = {mapped_val}")
        print(f"    The maximum element in ys was {max_ys}")
        print(f"    {x} <#> {max_ys} = {lhs}")
        print(f"    But max of mapped values is {rhs}")

    return result

def test_various_cases():
    """Test the distributivity property on various cases"""

    test_cases = [
        # (x, ys)
        (1, []),
        (1, [0]),
        (1, [2]),
        (1, [0, 2]),
        (1, [2, 1]),
        (1, [-1, 2]),
        (-1, [0]),
        (-1, [2]),
        (-1, [0, 2]),
        (-2, [1, 3]),
        (0, [1, 2]),
        (3, [0, 1, 2]),
        (-5, [2, 7, 3]),
    ]

    print("Testing nonNegPlus distributivity over maximum:")
    print("x <#> max(ys) = max(map (nonNegPlus x) ys)")
    print()

    passed = 0
    failed = 0

    for x, ys in test_cases:
        if test_distributivity(x, ys):
            passed += 1
        else:
            failed += 1
        print()

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_various_cases()
    if success:
        print("Distributivity property holds! This is the key lemma needed.")
    else:
        print("Property failed - need alternative approach.")