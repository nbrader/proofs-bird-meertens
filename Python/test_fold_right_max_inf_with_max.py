#!/usr/bin/env python3
"""
Test script for the fold_right_max_inf_with_max lemma.

This lemma states:
forall (xs : list Z) (m : Z),
  xs <> [] ->
  In m xs ->
  (forall y, In y xs -> y <= m) ->
  fold_right_max_inf xs = Z_val m.

In other words: If xs is non-empty, m is in xs, and m is >= all elements in xs,
then fold_right_max_inf xs = Z_val m.
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

def test_fold_right_max_inf_with_max_property(xs: List[int], m: int) -> bool:
    """
    Test the property:
    xs <> [] -> In m xs -> (forall y, In y xs -> y <= m) -> fold_right_max_inf xs = Z_val m
    """
    # Check preconditions
    if not xs:  # xs = []
        return True  # vacuous truth (premise is false)

    if m not in xs:  # not (In m xs)
        return True  # vacuous truth (premise is false)

    if not all(y <= m for y in xs):  # not (forall y, In y xs -> y <= m)
        return True  # vacuous truth (premise is false)

    # All preconditions met, check conclusion
    result = fold_right_max_inf(xs)
    expected = ZVal(m)

    return result == expected

def find_maximum_elements(xs: List[int]) -> List[int]:
    """Find all elements in xs that are equal to max(xs)"""
    if not xs:
        return []
    max_val = max(xs)
    return [x for x in xs if x == max_val]

def test_all_maximum_elements(xs: List[int]) -> bool:
    """Test the property for all maximum elements in xs"""
    if not xs:
        return True

    max_elements = find_maximum_elements(xs)

    for m in max_elements:
        if not test_fold_right_max_inf_with_max_property(xs, m):
            return False

    return True

def run_comprehensive_tests():
    """Run comprehensive tests for the fold_right_max_inf_with_max property"""
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

        # Lists where max appears multiple times
        [5, 3, 5, 1, 5], [2, 2, 2], [-1, -1, 0, -1],
    ]

    passed = 0
    failed = 0

    print("Testing fold_right_max_inf_with_max property...")
    print("=" * 60)

    for i, xs in enumerate(test_cases):
        try:
            result = test_all_maximum_elements(xs)
            if result:
                print(f"✓ Test {i+1}: {xs} - PASSED")
                passed += 1
            else:
                print(f"✗ Test {i+1}: {xs} - FAILED")
                # Debug information
                if xs:
                    max_elements = find_maximum_elements(xs)
                    fold_result = fold_right_max_inf(xs)
                    print(f"   Max elements: {max_elements}")
                    print(f"   fold_right_max_inf({xs}) = {fold_result}")
                    for m in max_elements:
                        individual_result = test_fold_right_max_inf_with_max_property(xs, m)
                        print(f"   Testing m={m}: {individual_result}")
                failed += 1
        except Exception as e:
            print(f"✗ Test {i+1}: {xs} - ERROR: {e}")
            failed += 1

    print("=" * 60)
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
            result = test_all_maximum_elements(xs)
            if result:
                random_passed += 1
            else:
                print(f"✗ Random test failed: {xs}")
                max_elements = find_maximum_elements(xs)
                fold_result = fold_right_max_inf(xs)
                print(f"   Max elements: {max_elements}")
                print(f"   fold_right_max_inf({xs}) = {fold_result}")
                random_failed += 1
        except Exception as e:
            print(f"✗ Random test error on {xs}: {e}")
            random_failed += 1

    print(f"Random tests: {random_passed} passed, {random_failed} failed")

    return failed == 0 and random_failed == 0

if __name__ == "__main__":
    success = run_comprehensive_tests()

    if success:
        print("\n🎉 All tests PASSED! The fold_right_max_inf_with_max lemma appears to be TRUE.")
        sys.exit(0)
    else:
        print("\n💥 Some tests FAILED! The lemma may be false or the implementation may be incorrect.")
        sys.exit(1)