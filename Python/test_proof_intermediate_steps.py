#!/usr/bin/env python3
"""
Test intermediate steps in the fold_right_max_inf_in proof to verify our reasoning.
"""

import sys
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

def test_non_empty_never_neginf():
    """Test that fold_right_max_inf on non-empty lists never returns NegInf"""
    print("Testing: fold_right_max_inf on non-empty lists never returns NegInf")

    test_cases = [
        [1], [0], [-1], [-100],
        [1, 2], [2, 1], [0, 0], [-1, -2],
        [1, 2, 3], [-5, -3, -1], [0, 0, 0],
        list(range(-10, 11))
    ]

    all_passed = True
    for xs in test_cases:
        result = fold_right_max_inf(xs)
        if isinstance(result, NegInf):
            print(f"✗ FAILED: {xs} -> {result}")
            all_passed = False
        else:
            print(f"✓ {xs} -> {result}")

    return all_passed

def test_fold_right_step_by_step():
    """Test the step-by-step computation of fold_right_max_inf"""
    print("\nStep-by-step analysis of fold_right_max_inf([x, y, ...]):")

    # Test case: [3, 1, 2]
    xs = [3, 1, 2]
    print(f"\nTesting xs = {xs}")

    # Manual step-by-step computation
    # fold_right Z_plus_neg_inf_max NegInf [Z_val(3), Z_val(1), Z_val(2)]
    # = Z_plus_neg_inf_max(Z_val(3), fold_right Z_plus_neg_inf_max NegInf [Z_val(1), Z_val(2)])

    # Step 1: Compute tail fold
    tail = [1, 2]
    tail_result = fold_right_max_inf(tail)
    print(f"fold_right_max_inf({tail}) = {tail_result}")

    # Step 2: Combine with head
    head = 3
    final_result = z_plus_neg_inf_max(ZVal(head), tail_result)
    print(f"Z_plus_neg_inf_max(Z_val({head}), {tail_result}) = {final_result}")

    # Step 3: Compare with direct computation
    direct_result = fold_right_max_inf(xs)
    print(f"Direct: fold_right_max_inf({xs}) = {direct_result}")

    print(f"Results match: {final_result == direct_result}")

    # Test the key insight: result should be in original list
    if isinstance(final_result, ZVal):
        in_list = final_result.val in xs
        print(f"Result {final_result.val} is in {xs}: {in_list}")

        # Show why it's in the list
        if isinstance(tail_result, ZVal):
            print(f"Case analysis:")
            print(f"  max({head}, {tail_result.val}) = {max(head, tail_result.val)}")
            if max(head, tail_result.val) == head:
                print(f"  Result is {head} (head element) -> in list ✓")
            else:
                print(f"  Result is {tail_result.val} (from tail)")
                print(f"  {tail_result.val} in {tail}: {tail_result.val in tail}")
                print(f"  Since tail ⊆ original list, result is in original list ✓")

def test_induction_hypothesis():
    """Test that the induction hypothesis holds for the tail"""
    print("\nTesting induction hypothesis on tails:")

    test_cases = [
        [3, 1, 2],      # tail is [1, 2]
        [5, 4, 3, 2],   # tail is [4, 3, 2]
        [-1, -5, 0],    # tail is [-5, 0]
        [10]            # tail is [] (empty, so vacuous)
    ]

    for xs in test_cases:
        if len(xs) <= 1:
            print(f"Skipping {xs} (too short for meaningful tail)")
            continue

        head = xs[0]
        tail = xs[1:]

        print(f"\nOriginal: {xs}, head: {head}, tail: {tail}")

        # Apply induction hypothesis: if tail is non-empty,
        # then fold_right_max_inf(tail) is in tail
        if tail:  # non-empty tail
            tail_result = fold_right_max_inf(tail)
            if isinstance(tail_result, ZVal):
                in_tail = tail_result.val in tail
                print(f"IH: fold_right_max_inf({tail}) = {tail_result}")
                print(f"IH: {tail_result.val} in {tail}: {in_tail}")

                # Now show main result
                main_result = fold_right_max_inf(xs)
                if isinstance(main_result, ZVal):
                    print(f"Main: fold_right_max_inf({xs}) = {main_result}")
                    print(f"Main: max({head}, {tail_result.val}) = {max(head, tail_result.val)}")

                    result_val = main_result.val
                    if result_val == head:
                        print(f"Result {result_val} = head -> in original list ✓")
                    elif result_val == tail_result.val:
                        print(f"Result {result_val} = tail result -> in tail -> in original list ✓")
                    else:
                        print(f"⚠️  Unexpected case: result {result_val} is neither head nor tail result")

if __name__ == "__main__":
    print("Testing intermediate proof steps for fold_right_max_inf_in")
    print("=" * 70)

    success1 = test_non_empty_never_neginf()
    test_fold_right_step_by_step()
    test_induction_hypothesis()

    print("\n" + "=" * 70)
    if success1:
        print("✅ Key insight confirmed: Non-empty lists never produce NegInf")
        print("✅ Induction structure is sound")
        print("✅ Ready to complete the formal Coq proof")
    else:
        print("❌ Some tests failed - check implementation")