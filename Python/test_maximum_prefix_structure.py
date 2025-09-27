#!/usr/bin/env python3
"""
Test the structure of maximum-achieving prefixes to understand why
nonNegPlus and regular addition agree for them in the mixed case.
"""

from typing import List

def nonNegPlus(x: int, y: int) -> int:
    return max(x + y, 0)

def fold_right_nonNegPlus(xs: List[int]) -> int:
    result = 0
    for x in reversed(xs):
        result = nonNegPlus(x, result)
    return result

def fold_right_add(xs: List[int]) -> int:
    return sum(xs)

def fold_right_max(xs: List[int]) -> int:
    result = 0
    for x in reversed(xs):
        result = max(x, result)
    return result

def inits(xs: List[int]) -> List[List[int]]:
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def mixed_signs(xs: List[int]) -> bool:
    has_pos = any(x > 0 for x in xs)
    has_nonpos = any(x <= 0 for x in xs)
    return has_pos and has_nonpos

def analyze_maximum_achieving_prefix_structure():
    """
    Analyze why maximum-achieving prefixes have the special property
    that nonNegSum p = sum p even though this doesn't hold in general.
    """

    print("Analysis of Maximum-Achieving Prefix Structure")
    print("=" * 60)

    test_cases = [
        [-1, 2, -1],
        [-2, 3, -1],
        [1, -2, 3],
        [-1, 1, -1, 2],
        [2, -3, 1],
        [-3, 5, -1],
        [1, -1, 2, -1],
    ]

    for xs in test_cases:
        if not mixed_signs(xs):
            continue

        print(f"\nInput: {xs}")
        print("-" * 40)

        prefixes = inits(xs)
        prefix_sums = [sum(p) for p in prefixes]
        prefix_nonNegSums = [fold_right_nonNegPlus(p) for p in prefixes]
        M = fold_right_max(prefix_sums)

        print(f"Prefixes: {prefixes}")
        print(f"Regular sums: {prefix_sums}")
        print(f"NonNeg sums: {prefix_nonNegSums}")
        print(f"Maximum M: {M}")

        # Find maximum-achieving prefixes
        max_achieving = []
        for i, p in enumerate(prefixes):
            if prefix_sums[i] == M:
                max_achieving.append((p, prefix_sums[i], prefix_nonNegSums[i]))

        print(f"Maximum-achieving prefixes: {max_achieving}")

        # Check the special property
        for p, regular_sum, nonNeg_sum in max_achieving:
            if regular_sum >= 0:  # Only check nonnegative cases
                agrees = (regular_sum == nonNeg_sum)
                print(f"  {p}: sum={regular_sum}, nonNegSum={nonNeg_sum}, agrees={agrees}")

                if not agrees:
                    print(f"    ❌ COUNTEREXAMPLE: Maximum-achieving prefix where nonNegSum ≠ sum!")
                    return p

        # Analyze intermediate computation paths for maximum-achieving prefixes
        print("Intermediate computation analysis:")
        for p, _, _ in max_achieving:
            if len(p) > 0:
                print(f"  For prefix {p}:")
                trace_computation_path(p)

def trace_computation_path(p: List[int]):
    """
    Trace the step-by-step computation for both regular sum and nonNegSum
    to understand why they agree for maximum-achieving prefixes.
    """
    if not p:
        return

    print(f"    Regular sum: {' + '.join(map(str, p))} = {sum(p)}")

    # Trace nonNegSum computation from right to left
    result = 0
    steps = []
    for x in reversed(p):
        old_result = result
        result = nonNegPlus(x, result)
        steps.append(f"nonNegPlus({x}, {old_result}) = max({x + old_result}, 0) = {result}")

    print(f"    NonNegSum computation:")
    for step in reversed(steps):
        print(f"      {step}")

def test_counterexample_for_general_claim():
    """
    Confirm that the general claim "sum >= 0 → nonNegSum = sum" is false,
    but check if it might hold for maximum-achieving prefixes specifically.
    """
    print(f"\n{'='*60}")
    print("Testing general claim vs maximum-achieving prefix property")
    print("-" * 60)

    # Known counterexample to general claim
    p_counter = [2, -1]
    regular = sum(p_counter)
    nonNeg = fold_right_nonNegPlus(p_counter)

    print(f"General claim counterexample: {p_counter}")
    print(f"  sum = {regular} >= 0, but nonNegSum = {nonNeg} ≠ sum")
    print(f"  This shows sum >= 0 ⇏ nonNegSum = sum in general")

    # But check if this prefix can be maximum-achieving in some mixed-sign list
    # Try to construct a list where [2, -1] is a maximum-achieving prefix
    test_lists = [
        [2, -1, -2],  # [2, -1] might be max-achieving here
        [2, -1, 0],
        [2, -1, 1, -3],
    ]

    for xs in test_lists:
        if mixed_signs(xs):
            prefixes = inits(xs)
            prefix_sums = [sum(p) for p in prefixes]
            M = max(prefix_sums)

            if p_counter in prefixes:
                p_index = prefixes.index(p_counter)
                p_sum = prefix_sums[p_index]
                is_max_achieving = (p_sum == M)

                print(f"  In list {xs}: {p_counter} achieves max? {is_max_achieving}")
                if is_max_achieving:
                    print(f"    ❌ Found maximum-achieving prefix that violates nonNegSum = sum!")

if __name__ == "__main__":
    counterexample = analyze_maximum_achieving_prefix_structure()
    test_counterexample_for_general_claim()

    if counterexample:
        print(f"\n🚨 FOUND COUNTEREXAMPLE: {counterexample}")
        print("The lemma logic may be false!")
    else:
        print(f"\n✅ Maximum-achieving prefixes appear to satisfy nonNegSum = sum")
        print("The lemma logic seems sound, but requires sophisticated proof techniques.")