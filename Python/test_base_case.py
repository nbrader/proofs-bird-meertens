#!/usr/bin/env python3
"""
Test the base case for nonNegPlus_max_distribute_map:
x <#> fold_right Z.max 0 [] = fold_right Z.max 0 (map (nonNegPlus x) [])

This should be:
x <#> 0 = 0

Let's see if this is actually true.
"""

def nonNegPlus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def test_base_case(x):
    """Test: x <#> 0 = 0"""
    lhs = nonNegPlus(x, 0)
    rhs = 0
    print(f"x = {x}: x <#> 0 = {lhs}, expected = {rhs}, equal = {lhs == rhs}")
    return lhs == rhs

def test_cases():
    """Test various values of x"""
    test_values = [-5, -1, 0, 1, 5]

    print("Testing base case: x <#> 0 = 0")
    print()

    passed = 0
    failed = 0

    for x in test_values:
        if test_base_case(x):
            passed += 1
        else:
            failed += 1

    print(f"\nResults: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("Base case property holds!")
    else:
        print("Base case property does NOT hold!")