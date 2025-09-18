#!/usr/bin/env python3
"""
Test script for the fold_right_max_inf_in lemma.

This lemma states: forall (xs : list Z), xs <> [] -> Z_plus_neg_inf_In (fold_right_max_inf xs) xs.

In other words: If xs is non-empty, then fold_right_max_inf xs returns an element that is in xs.
"""

import sys
import random
from typing import List, Union, Optional

# Z_plus_neg_inf type simulation
class NegInf:
    def __repr__(self):
        return "NegInf"

    def __eq__(self, other):
        return isinstance(other, NegInf)

class ZVal:
    def __init__(self, val: int):
        self.val = val

    def __repr__(self):
        return f"Z_val({self.val})"

    def __eq__(self, other):
        return isinstance(other, ZVal) and self.val == other.val

ZPlusNegInf = Union[ZVal, NegInf]

def z_plus_neg_inf_max(x: ZPlusNegInf, y: ZPlusNegInf) -> ZPlusNegInf:
    """Z_plus_neg_inf_max operation"""
    if isinstance(x, NegInf):
        return y
    if isinstance(y, NegInf):
        return x
    # Both are ZVal
    return ZVal(max(x.val, y.val))

def fold_right_max_inf(xs: List[int]) -> ZPlusNegInf:
    """
    fold_right_max_inf xs = fold_right Z_plus_neg_inf_max NegInf (map Z_val xs)
    """
    if not xs:
        return NegInf()

    result = NegInf()
    # fold_right goes from right to left
    for x in reversed(xs):
        result = z_plus_neg_inf_max(ZVal(x), result)

    return result

def z_plus_neg_inf_in(x: ZPlusNegInf, xs: List[int]) -> bool:
    """
    Z_plus_neg_inf_In x xs = match x with | NegInf => False | Z_val z => In z xs
    """
    if isinstance(x, NegInf):
        return False
    return x.val in xs

def test_fold_right_max_inf_in_property(xs: List[int]) -> bool:
    """
    Test the property: xs <> [] -> Z_plus_neg_inf_In (fold_right_max_inf xs) xs
    """
    if not xs:  # xs = []
        return True  # vacuous truth (premise is false)

    result = fold_right_max_inf(xs)
    return z_plus_neg_inf_in(result, xs)

def run_comprehensive_tests():
    """Run comprehensive tests for the fold_right_max_inf_in property"""
    test_cases = [
        # Single element lists
        [1], [-1], [0], [100], [-100],

        # Two element lists
        [1, 2], [2, 1], [-1, 1], [1, -1], [0, 0],

        # Three element lists
        [1, 2, 3], [3, 2, 1], [1, 3, 2], [-1, 0, 1],

        # Lists with duplicates
        [5, 5, 5], [1, 2, 1], [3, 1, 3, 1],

        # All negative lists
        [-5, -3, -1], [-10, -20, -30],

        # All positive lists
        [1, 3, 5], [10, 20, 30],

        # Mixed lists
        [-5, 0, 5], [-10, 5, -3, 8],

        # Larger lists
        list(range(1, 11)),  # [1, 2, ..., 10]
        list(range(-10, 1)), # [-10, -9, ..., 0]
        [-5, -3, -1, 1, 3, 5],
    ]

    passed = 0
    failed = 0

    print("Testing fold_right_max_inf_in property...")
    print("=" * 50)

    for i, xs in enumerate(test_cases):
        try:
            result = test_fold_right_max_inf_in_property(xs)
            if result:
                print(f"✓ Test {i+1}: {xs} - PASSED")
                passed += 1
            else:
                print(f"✗ Test {i+1}: {xs} - FAILED")
                # Debug information
                fold_result = fold_right_max_inf(xs)
                in_result = z_plus_neg_inf_in(fold_result, xs)
                print(f"   fold_right_max_inf({xs}) = {fold_result}")
                print(f"   z_plus_neg_inf_in({fold_result}, {xs}) = {in_result}")
                failed += 1
        except Exception as e:
            print(f"✗ Test {i+1}: {xs} - ERROR: {e}")
            failed += 1

    print("=" * 50)
    print(f"Results: {passed} passed, {failed} failed")

    # Random testing
    print("\nRunning random tests...")
    random_passed = 0
    random_failed = 0

    for _ in range(200):
        # Generate random list of length 1-20
        length = random.randint(1, 20)
        xs = [random.randint(-50, 50) for _ in range(length)]

        try:
            result = test_fold_right_max_inf_in_property(xs)
            if result:
                random_passed += 1
            else:
                print(f"✗ Random test failed: {xs}")
                fold_result = fold_right_max_inf(xs)
                in_result = z_plus_neg_inf_in(fold_result, xs)
                print(f"   fold_right_max_inf({xs}) = {fold_result}")
                print(f"   z_plus_neg_inf_in({fold_result}, {xs}) = {in_result}")
                random_failed += 1
        except Exception as e:
            print(f"✗ Random test error on {xs}: {e}")
            random_failed += 1

    print(f"Random tests: {random_passed} passed, {random_failed} failed")

    return failed == 0 and random_failed == 0

if __name__ == "__main__":
    success = run_comprehensive_tests()

    if success:
        print("\n🎉 All tests PASSED! The fold_right_max_inf_in lemma appears to be TRUE.")
        sys.exit(0)
    else:
        print("\n💥 Some tests FAILED! The lemma may be false or the implementation may be incorrect.")
        sys.exit(1)