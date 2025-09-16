#!/usr/bin/env python3
"""
Test what the CORRECT base case for nonNegPlus_max_distribute_map should be:
x <#> fold_right Z.max 0 [] = fold_right Z.max 0 (map (nonNegPlus x) [])

LHS: x <#> 0
RHS: fold_right Z.max 0 [] = 0

So I need: x <#> 0 = 0, but that's false.

Wait, let me check the actual goal more carefully.
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

def test_actual_base_case(x):
    """Test the ACTUAL base case"""
    # LHS: x <#> fold_right Z.max 0 []
    lhs = nonNegPlus(x, fold_right(z_max, 0, []))

    # RHS: fold_right Z.max 0 (map (nonNegPlus x) [])
    mapped = [nonNegPlus(x, y) for y in []]
    rhs = fold_right(z_max, 0, mapped)

    print(f"x = {x}")
    print(f"  LHS: x <#> fold_right Z.max 0 [] = {x} <#> 0 = {lhs}")
    print(f"  RHS: fold_right Z.max 0 (map (nonNegPlus {x}) []) = fold_right Z.max 0 [] = {rhs}")
    print(f"  Equal: {lhs == rhs}")

    return lhs == rhs

def test_cases():
    """Test various values of x"""
    test_values = [-5, -1, 0, 1, 5]

    print("Testing ACTUAL base case:")
    print("x <#> fold_right Z.max 0 [] = fold_right Z.max 0 (map (nonNegPlus x) [])")
    print()

    passed = 0
    failed = 0

    for x in test_values:
        if test_actual_base_case(x):
            passed += 1
        else:
            failed += 1
        print()

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("Actual base case property holds!")
    else:
        print("Actual base case property does NOT hold!")