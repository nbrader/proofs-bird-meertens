#!/usr/bin/env python3
"""
Test the fold_right_max_membership property:
If fold_right Z.max 0 l > 0, then the result appears in l.
"""

from typing import List

def fold_right_max(xs: List[int]) -> int:
    result = 0
    for x in reversed(xs):
        result = max(x, result)
    return result

def test_fold_right_max_membership():
    """
    Test: If fold_right Z.max 0 l > 0, then the result is in l.
    """
    print("Testing fold_right_max_membership property")
    print("=" * 50)

    test_cases = [
        [1],           # max = 1, in list
        [1, 2],        # max = 2, in list
        [2, 1],        # max = 2, in list
        [-1, 3, -2],   # max = 3, in list
        [5, -3, 2],    # max = 5, in list
        [0, 4, -1],    # max = 4, in list
        [-2, -1],      # max = 0, not in list (but max = 0, so condition doesn't apply)
        [],            # max = 0, empty list
        [-5, -3, -1],  # max = 0, condition doesn't apply
        [3, 0, -1],    # max = 3, in list
    ]

    for l in test_cases:
        max_result = fold_right_max(l)

        print(f"List: {l}")
        print(f"  fold_right_max = {max_result}")

        if max_result > 0:
            in_list = max_result in l
            print(f"  max > 0: {max_result} in list? {in_list}")
            if not in_list:
                print(f"  ❌ COUNTEREXAMPLE: max={max_result} > 0 but not in {l}")
                return l
        else:
            print(f"  max <= 0: condition doesn't apply")
        print()

    print("✅ All test cases pass - property holds")
    return None

def test_edge_cases():
    """Test edge cases for the membership property"""
    print("Testing edge cases:")
    print("-" * 30)

    # Edge case: multiple occurrences of maximum
    l = [3, 1, 3, 2]
    max_result = fold_right_max(l)
    print(f"Multiple max case {l}: max = {max_result}, in list = {max_result in l}")

    # Edge case: maximum at different positions
    for l in [[5, 1, 2], [1, 5, 2], [1, 2, 5]]:
        max_result = fold_right_max(l)
        print(f"Max at different pos {l}: max = {max_result}, in list = {max_result in l}")

def verify_fold_right_semantics():
    """Verify our Python fold_right_max matches the Coq semantics"""
    print(f"\nVerifying fold_right semantics:")
    print("-" * 35)

    # Test with step-by-step computation
    test_list = [2, -1, 3]
    print(f"Computing fold_right Z.max 0 {test_list} step by step:")

    # Coq: fold_right Z.max 0 [2; -1; 3] = Z.max 2 (Z.max (-1) (Z.max 3 0))
    step1 = max(3, 0)  # Z.max 3 0
    print(f"  Step 1: max(3, 0) = {step1}")

    step2 = max(-1, step1)  # Z.max (-1) step1
    print(f"  Step 2: max(-1, {step1}) = {step2}")

    step3 = max(2, step2)  # Z.max 2 step2
    print(f"  Step 3: max(2, {step2}) = {step3}")

    python_result = fold_right_max(test_list)
    print(f"  Python result: {python_result}")
    print(f"  Match: {step3 == python_result}")

if __name__ == "__main__":
    counterexample = test_fold_right_max_membership()
    test_edge_cases()
    verify_fold_right_semantics()

    if counterexample:
        print(f"\n🚨 COUNTEREXAMPLE FOUND: {counterexample}")
        print("The property is false!")
    else:
        print(f"\n✅ Property verified: fold_right Z.max 0 l > 0 → result ∈ l")