#!/usr/bin/env python3
"""
Test implicit claims from comments in TropicalMaxSegSum.v

This script tests various implicit claims made in comments that might be false.
"""

import itertools
from typing import List, Optional

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

def test_claim_nonneg_monotonic() -> List[str]:
    """
    Test implicit claim from line 105 comment:
    "When all elements in suffix are >= 0, nonNegSum is monotonic"

    This claims that if suffix is all nonnegative, then:
    nonNegSum prefix <= nonNegSum (prefix ++ suffix)
    """
    counterexamples = []

    # Generate test cases
    for prefix_len in range(1, 4):
        for suffix_len in range(1, 4):
            for prefix in itertools.product(range(-3, 4), repeat=prefix_len):
                for suffix in itertools.product(range(0, 4), repeat=suffix_len):  # All nonnegative
                    prefix_list = list(prefix)
                    suffix_list = list(suffix)
                    combined = prefix_list + suffix_list

                    prefix_sum = fold_right_nonNegPlus(prefix_list)
                    combined_sum = fold_right_nonNegPlus(combined)

                    if prefix_sum > combined_sum:
                        counterexamples.append(
                            f"prefix={prefix_list}, suffix={suffix_list}, "
                            f"nonNegSum(prefix)={prefix_sum} > nonNegSum(combined)={combined_sum}"
                        )

    return counterexamples

def test_claim_entire_list_in_inits() -> List[str]:
    """
    Test implicit claim from line 72 comment:
    "The entire list xs is always the last element of inits xs"
    """
    counterexamples = []

    for length in range(1, 6):
        for values in itertools.product(range(-2, 3), repeat=length):
            xs = list(values)
            inits_xs = inits(xs)

            if len(inits_xs) == 0 or inits_xs[-1] != xs:
                counterexamples.append(f"xs={xs}, inits(xs)={inits_xs}, last != xs")

    return counterexamples

def test_claim_tropical_finite_preservation() -> List[str]:
    """
    Test implicit claim from line 244-245 comment:
    "the result must be the same as our computational model"

    This is about tropical operations always producing finite results.
    """
    counterexamples = []

    # Test that our nonNegPlus model actually corresponds to the claimed tropical behavior
    for length in range(1, 5):
        for values in itertools.product(range(-5, 6), repeat=length):
            xs = list(values)

            # The claimed result should be max(0, max subarray sum)
            # Let's verify this matches nonNegSum
            nonNeg_result = fold_right_nonNegPlus(xs)

            # Compute all subarray sums
            all_subarray_sums = []
            for i in range(len(xs)):
                for j in range(i, len(xs)):
                    subarray = xs[i:j+1]
                    all_subarray_sums.append(sum(subarray))

            max_subarray = max(all_subarray_sums) if all_subarray_sums else 0
            expected_result = max(0, max_subarray)

            # This is actually testing Kadane's algorithm correctness!
            # But the comment suggests this should hold...
            if nonNeg_result != expected_result:
                counterexamples.append(
                    f"xs={xs}, nonNegSum={nonNeg_result} != max(0, max_subarray)={expected_result}, "
                    f"max_subarray={max_subarray}"
                )

    return counterexamples

def test_claim_all_nonpositive_gives_zero() -> List[str]:
    """
    Test implicit claim that all non-positive lists give nonNegSum = 0
    """
    counterexamples = []

    for length in range(1, 5):
        for values in itertools.product(range(-5, 1), repeat=length):  # All <= 0
            xs = list(values)
            if all_nonpositive(xs):
                result = fold_right_nonNegPlus(xs)
                if result != 0:
                    counterexamples.append(f"all_nonpositive xs={xs}, but nonNegSum={result} != 0")

    return counterexamples

def test_claim_mixed_case_max_nonneg() -> List[str]:
    """
    Test claim from line 437 comment:
    "Since we're taking max with 0, the result is always >= 0"

    This is about max_subarray_sum_nonneg_in_mixed_case
    """
    counterexamples = []

    for length in range(2, 5):
        for values in itertools.product(range(-3, 4), repeat=length):
            xs = list(values)
            if mixed_signs(xs):
                prefix_sums = [fold_right_add(p) for p in inits(xs)]
                max_result = fold_right_max(prefix_sums)

                if max_result < 0:
                    counterexamples.append(f"mixed_signs xs={xs}, but max prefix sum={max_result} < 0")

    return counterexamples

def test_claim_maximum_achieved_by_element() -> List[str]:
    """
    Test implicit claim from line 717-718 comment:
    "fold_right Z.max 0 l finds the maximum element in l"
    "So there must exist some element in l that equals this maximum"
    """
    counterexamples = []

    # This should always be true, but let's verify
    for length in range(1, 6):
        for values in itertools.product(range(-3, 4), repeat=length):
            l = list(values)
            max_result = fold_right_max(l)

            # Check if max_result is achieved by some element or by the base (0)
            if max_result not in l and max_result != 0:
                counterexamples.append(f"list={l}, max={max_result}, not in list and != 0")

    return counterexamples

def test_all_implicit_claims():
    """Test all implicit claims found in comments"""
    print("Testing implicit claims from comments in TropicalMaxSegSum.v")
    print("=" * 80)

    tests = [
        ("nonNegSum monotonicity with nonneg suffix", test_claim_nonneg_monotonic),
        ("entire list is last element of inits", test_claim_entire_list_in_inits),
        ("tropical finite preservation", test_claim_tropical_finite_preservation),
        ("all nonpositive gives zero", test_claim_all_nonpositive_gives_zero),
        ("mixed case max is nonnegative", test_claim_mixed_case_max_nonneg),
        ("maximum achieved by element", test_claim_maximum_achieved_by_element),
    ]

    any_failures = False

    for test_name, test_func in tests:
        print(f"\nTesting: {test_name}")
        print("-" * 50)

        counterexamples = test_func()

        if counterexamples:
            print(f"❌ Found {len(counterexamples)} counterexamples:")
            for i, ex in enumerate(counterexamples[:5]):  # Show first 5
                print(f"  {i+1}. {ex}")
            if len(counterexamples) > 5:
                print(f"  ... and {len(counterexamples) - 5} more")
            any_failures = True
        else:
            print("✅ No counterexamples found")

    print("\n" + "=" * 80)
    if any_failures:
        print("❌ Some implicit claims from comments may be false!")
    else:
        print("✅ All implicit claims from comments appear correct")

if __name__ == "__main__":
    test_all_implicit_claims()