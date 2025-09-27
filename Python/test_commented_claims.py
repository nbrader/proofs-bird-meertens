#!/usr/bin/env python3
"""
Test specific mathematical claims found in comments of TropicalMaxSegSum.v

These are implicit goals and subgoals that might be assumed but not proven.
"""

import itertools
from typing import List, Optional, Tuple

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

def all_nonnegative(xs: List[int]) -> bool:
    return all(x >= 0 for x in xs)

def all_nonpositive(xs: List[int]) -> bool:
    return all(x <= 0 for x in xs)

def mixed_signs(xs: List[int]) -> bool:
    return not all_nonnegative(xs) and not all_nonpositive(xs)

def test_claim_nonneg_monotonic_suffixes() -> List[str]:
    """
    Line 64-65 claim: "When all elements are >= 0, adding elements never decreases the sum"
    Line 105 claim: "When all elements in suffix are >= 0, nonNegSum is monotonic"

    Test: For prefix + suffix where suffix is all nonnegative:
    nonNegSum(prefix) <= nonNegSum(prefix ++ suffix)
    """
    counterexamples = []

    for prefix_len in range(1, 4):
        for suffix_len in range(1, 4):
            for prefix in itertools.product(range(-3, 4), repeat=prefix_len):
                for suffix in itertools.product(range(1, 4), repeat=suffix_len):  # All positive
                    prefix_list = list(prefix)
                    suffix_list = list(suffix)
                    combined = prefix_list + suffix_list

                    prefix_sum = fold_right_nonNegPlus(prefix_list)
                    combined_sum = fold_right_nonNegPlus(combined)

                    if prefix_sum > combined_sum:
                        counterexamples.append(
                            f"prefix={prefix_list}, suffix={suffix_list}: "
                            f"nonNegSum(prefix)={prefix_sum} > nonNegSum(combined)={combined_sum}"
                        )

    return counterexamples

def test_claim_maximum_achieved_by_list_element() -> List[str]:
    """
    Line 709 claim: "The maximum of fold_right Z.max 0 (map f l) for non-empty l must equal f x for some x in l"
    Line 717-718 claim: "fold_right Z.max 0 l finds the maximum element in l"

    Test: For any non-empty list l, fold_right Z.max 0 l equals some element in l or 0
    """
    counterexamples = []

    for length in range(1, 5):
        for values in itertools.product(range(-5, 3), repeat=length):  # Include negatives
            l = list(values)
            max_result = fold_right_max(l)

            # The maximum should either be 0 (base) or some element in the list
            if max_result != 0 and max_result not in l:
                counterexamples.append(f"list={l}, max={max_result} not in list and != 0")

    return counterexamples

def test_claim_nonpositive_implies_zero() -> List[str]:
    """
    Line 166-167 claim: "When all elements are non-positive, nonNegSum clamps to 0"

    Test: all_nonpositive(xs) -> nonNegSum(xs) = 0
    """
    counterexamples = []

    for length in range(1, 5):
        for values in itertools.product(range(-5, 1), repeat=length):  # All <= 0
            xs = list(values)
            if all_nonpositive(xs):
                result = fold_right_nonNegPlus(xs)
                if result != 0:
                    counterexamples.append(f"all_nonpositive xs={xs} but nonNegSum={result} != 0")

    return counterexamples

def test_claim_contradiction_in_nonpositive_case() -> List[str]:
    """
    Line 142 claim: "This contradicts our assumption that all elements are non-positive"

    Context: In all-nonpositive case, if x + nonNegSum(xs') >= 0, this should be impossible.
    Test: For all_nonpositive list (x::xs'), is x + nonNegSum(xs') >= 0 actually impossible?
    """
    counterexamples = []

    for length in range(1, 4):
        for values in itertools.product(range(-3, 1), repeat=length):  # All <= 0
            if length == 0:
                continue
            xs = list(values)
            if all_nonpositive(xs):
                x = xs[0]
                xs_tail = xs[1:]

                tail_nonNegSum = fold_right_nonNegPlus(xs_tail)
                sum_with_head = x + tail_nonNegSum

                if sum_with_head >= 0:
                    counterexamples.append(
                        f"all_nonpositive xs={xs}: x={x}, nonNegSum(tail)={tail_nonNegSum}, "
                        f"x + nonNegSum(tail)={sum_with_head} >= 0 (should be impossible)"
                    )

    return counterexamples

def test_claim_nonneg_equals_add_for_nonneg_result() -> List[str]:
    """
    Line 814-815 claim: "If fold_right Z.add 0 p >= 0, then at every intermediate step,
    the partial sum computed by nonNegPlus should equal the partial sum computed by Z.add"

    Test: If sum(p) >= 0, does nonNegSum(p) = sum(p)?
    """
    counterexamples = []

    for length in range(1, 5):
        for values in itertools.product(range(-3, 4), repeat=length):
            p = list(values)
            regular_sum = sum(p)

            if regular_sum >= 0:
                nonNeg_sum = fold_right_nonNegPlus(p)
                if nonNeg_sum != regular_sum:
                    counterexamples.append(
                        f"sum(p)={regular_sum} >= 0 but nonNegSum(p)={nonNeg_sum} != sum(p), p={p}"
                    )

    return counterexamples

def test_claim_prefix_equality_for_max_achieving() -> List[str]:
    """
    Line 891-893 claim: "For any prefix p in inits xs:
    - If fold_right Z.add 0 p >= 0, then fold_right nonNegPlus 0 p = fold_right Z.add 0 p"

    Test this for prefixes that achieve the maximum.
    """
    counterexamples = []

    for length in range(2, 5):
        for values in itertools.product(range(-3, 4), repeat=length):
            xs = list(values)
            if mixed_signs(xs):
                prefixes = inits(xs)
                regular_sums = [sum(p) for p in prefixes]
                max_regular = fold_right_max(regular_sums)

                # Find prefixes that achieve the maximum
                for i, p in enumerate(prefixes):
                    p_sum = regular_sums[i]
                    if p_sum == max_regular and p_sum >= 0:
                        # This prefix achieves max and has nonneg sum
                        nonNeg_sum = fold_right_nonNegPlus(p)
                        if nonNeg_sum != p_sum:
                            counterexamples.append(
                                f"xs={xs}, max-achieving prefix p={p}: "
                                f"sum(p)={p_sum} >= 0 but nonNegSum(p)={nonNeg_sum} != sum(p)"
                            )

    return counterexamples

def test_claim_entire_list_always_last_in_inits() -> List[str]:
    """
    Line 72 claim: "The entire list xs is always the last element of inits xs"

    Test: inits(xs)[-1] == xs for all xs
    """
    counterexamples = []

    for length in range(0, 6):
        for values in itertools.product(range(-2, 3), repeat=length):
            xs = list(values)
            inits_xs = inits(xs)

            if len(inits_xs) == 0:
                counterexamples.append(f"inits({xs}) is empty")
            elif inits_xs[-1] != xs:
                counterexamples.append(f"inits({xs})[-1] = {inits_xs[-1]} != {xs}")

    return counterexamples

def test_claim_max_preserved_value() -> List[str]:
    """
    Line 724 claim: "In our specific context, we know M >= 0, so there exists some prefix
    with nonnegative sum, which means that prefix's value is preserved in the maximum"

    Test: If M >= 0 where M = max(prefix_sums), then there exists a prefix p where:
    - sum(p) >= 0
    - sum(p) = M
    """
    counterexamples = []

    for length in range(2, 5):
        for values in itertools.product(range(-3, 4), repeat=length):
            xs = list(values)
            if mixed_signs(xs):
                prefixes = inits(xs)
                prefix_sums = [sum(p) for p in prefixes]
                M = fold_right_max(prefix_sums)

                if M >= 0:
                    # Check if there exists a prefix with nonneg sum achieving M
                    found_nonneg_achiever = False
                    for i, p in enumerate(prefixes):
                        p_sum = prefix_sums[i]
                        if p_sum >= 0 and p_sum == M:
                            found_nonneg_achiever = True
                            break

                    if not found_nonneg_achiever:
                        counterexamples.append(
                            f"xs={xs}, M={M} >= 0, but no prefix has nonneg sum = M. "
                            f"prefix_sums={prefix_sums}"
                        )

    return counterexamples

def run_all_comment_tests():
    """Run all tests for claims made in comments"""
    print("Testing Mathematical Claims from Comments")
    print("=" * 80)

    tests = [
        ("nonNegSum monotonic with nonneg suffixes", test_claim_nonneg_monotonic_suffixes),
        ("maximum achieved by list element", test_claim_maximum_achieved_by_list_element),
        ("nonpositive implies zero", test_claim_nonpositive_implies_zero),
        ("contradiction in nonpositive case", test_claim_contradiction_in_nonpositive_case),
        ("nonNeg equals add for nonneg result", test_claim_nonneg_equals_add_for_nonneg_result),
        ("prefix equality for max achieving", test_claim_prefix_equality_for_max_achieving),
        ("entire list always last in inits", test_claim_entire_list_always_last_in_inits),
        ("max preserved value claim", test_claim_max_preserved_value),
    ]

    total_issues = 0

    for test_name, test_func in tests:
        print(f"\nTesting: {test_name}")
        print("-" * 50)

        counterexamples = test_func()

        if counterexamples:
            print(f"❌ Found {len(counterexamples)} counterexamples:")
            for i, ex in enumerate(counterexamples[:3]):  # Show first 3
                print(f"  {i+1}. {ex}")
            if len(counterexamples) > 3:
                print(f"  ... and {len(counterexamples) - 3} more")
            total_issues += len(counterexamples)
        else:
            print("✅ No counterexamples found")

    print(f"\n{'='*80}")
    if total_issues > 0:
        print(f"❌ TOTAL: {total_issues} counterexamples to commented claims found!")
        print("Some implicit assumptions in comments may be false.")
    else:
        print("✅ All mathematical claims in comments appear correct.")

if __name__ == "__main__":
    run_all_comment_tests()