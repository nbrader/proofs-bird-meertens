#!/usr/bin/env python3
"""
Verify the fold_right_max_inf_with_max lemma computationally.
This lemma states: if m is in xs, m is the maximum of xs, and xs is non-empty,
then fold_right_max_inf xs = Z_val m.
"""

from typing import List, Union

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
    """fold_right_max_inf xs = fold_right Z_plus_neg_inf_max NegInf (map Z_val xs)"""
    if not xs:
        return NegInf()

    result = NegInf()
    # fold_right goes from right to left
    for x in reversed(xs):
        result = z_plus_neg_inf_max(ZVal(x), result)

    return result

def test_lemma_conditions(xs: List[int], m: int) -> bool:
    """Test the three conditions of the lemma"""
    if not xs:  # xs must be non-empty
        return False

    if m not in xs:  # m must be in xs
        return False

    # m must be the maximum (all elements <= m)
    if not all(y <= m for y in xs):
        return False

    return True

def test_lemma_conclusion(xs: List[int], m: int) -> bool:
    """Test that fold_right_max_inf xs = Z_val m"""
    result = fold_right_max_inf(xs)
    expected = ZVal(m)
    return result == expected

def test_fold_right_max_inf_with_max():
    """Test the complete lemma"""
    print("Testing fold_right_max_inf_with_max lemma")
    print("=" * 60)

    test_cases = [
        # Simple cases
        ([5], 5),
        ([3, 7], 7),
        ([7, 3], 7),
        ([1, 2, 3], 3),
        ([3, 2, 1], 3),
        ([5, 5, 5], 5),

        # Negative numbers
        ([-1, -5, -3], -1),
        ([-10, -2, -7], -2),
        ([0, -1, -2], 0),

        # Mixed positive/negative
        ([-5, 0, 3, -2], 3),
        ([10, -5, 7, 2], 10),

        # Edge cases
        ([0], 0),
        ([-100], -100),
        ([100, 50, 75, 25], 100),

        # Longer lists
        ([1, 5, 3, 9, 2, 7], 9),
        ([-3, -1, -7, -2, -10], -1),
        ([0, 0, 0, 0], 0),
    ]

    passed = 0
    total = 0

    for xs, m in test_cases:
        total += 1

        # Check conditions
        conditions_ok = test_lemma_conditions(xs, m)
        if not conditions_ok:
            print(f"❌ Test {total}: {xs}, m={m} - conditions not met")
            continue

        # Check conclusion
        conclusion_ok = test_lemma_conclusion(xs, m)

        if conclusion_ok:
            passed += 1
            print(f"✅ Test {total}: {xs}, m={m} - PASS")
        else:
            result = fold_right_max_inf(xs)
            print(f"❌ Test {total}: {xs}, m={m} - FAIL")
            print(f"   Expected: Z_val({m}), Got: {result}")

    print(f"\nResults: {passed}/{total} tests passed")

    # Also test some invalid cases to make sure we understand the conditions
    print(f"\nTesting invalid cases (should fail conditions):")
    invalid_cases = [
        ([], 0),        # empty list
        ([1, 2, 3], 5), # m not in list
        ([1, 2, 3], 2), # m not maximum
        ([5, 8, 3], 5), # m not maximum
    ]

    for xs, m in invalid_cases:
        conditions_ok = test_lemma_conditions(xs, m)
        print(f"Invalid case {xs}, m={m}: conditions met = {conditions_ok}")

    return passed == total

def analyze_fold_computation():
    """Analyze how the fold works step by step"""
    print(f"\nDetailed analysis of fold_right_max_inf computation:")
    print("=" * 60)

    test_case = [3, 1, 4, 2]
    m = 4

    print(f"Case: xs = {test_case}, m = {m}")
    print(f"Conditions: m in xs = {m in test_case}, m is max = {all(x <= m for x in test_case)}")

    print(f"\nStep-by-step fold_right computation:")
    print(f"fold_right Z_plus_neg_inf_max NegInf [Z_val(3), Z_val(1), Z_val(4), Z_val(2)]")

    # Manual computation
    result = NegInf()
    print(f"Start: result = {result}")

    for i, x in enumerate(reversed(test_case)):
        old_result = result
        result = z_plus_neg_inf_max(ZVal(x), result)
        step = i + 1
        print(f"Step {step}: Z_val({x}) ∨_inf {old_result} = {result}")

    print(f"\nFinal result: {result}")
    print(f"Expected: Z_val({m})")
    print(f"Match: {result == ZVal(m)}")

if __name__ == "__main__":
    success = test_fold_right_max_inf_with_max()
    analyze_fold_computation()

    print(f"\n{'='*60}")
    if success:
        print("✅ ALL TESTS PASSED - Lemma is computationally verified as TRUE")
        print("The Coq proof should be completable")
    else:
        print("❌ SOME TESTS FAILED - Check lemma statement or implementation")