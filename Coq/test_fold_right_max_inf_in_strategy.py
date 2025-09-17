#!/usr/bin/env python3
"""
Analyze the structure of fold_right_max_inf_in lemma to develop proof strategy.

Lemma: forall (xs : list Z), xs <> [] -> Z_plus_neg_inf_In (fold_right_max_inf xs) xs.

This means: For non-empty list xs, fold_right_max_inf(xs) returns Z_val(z) where z ∈ xs.

Key insights for proof strategy:
1. Base case: [x] -> fold_right gives Z_val(x), and x ∈ [x] ✓
2. Inductive case: x::xs -> fold_right gives max(x, fold_right(xs))
   - If result = x, then x ∈ x::xs ✓
   - If result = fold_right(xs), then by IH, it's in xs, so it's in x::xs ✓

Let's test these structural insights.
"""

from typing import Union, List
import random

# Type definitions
class NegInf:
    def __repr__(self):
        return "NegInf"
    def __eq__(self, other):
        return isinstance(other, NegInf)

Z_plus_neg_inf = Union[int, NegInf]

def z_plus_neg_inf_max(x: Z_plus_neg_inf, y: Z_plus_neg_inf) -> Z_plus_neg_inf:
    """Max operation for Z_plus_neg_inf"""
    if isinstance(x, NegInf):
        return y
    if isinstance(y, NegInf):
        return x
    # Both are integers
    return max(x, y)

def fold_right_max_inf(xs: List[int]) -> Z_plus_neg_inf:
    """fold_right Z_plus_neg_inf_max NegInf (map Z_val xs)"""
    if not xs:
        return NegInf()

    result = NegInf()
    for x in reversed(xs):  # fold_right processes from right to left
        result = z_plus_neg_inf_max(x, result)

    return result

def test_base_case():
    """Test base case: [x] -> result = x and x ∈ [x]"""
    print("=== Testing Base Case: [x] ===")

    test_values = [1, -1, 0, 100, -50]

    for x in test_values:
        result = fold_right_max_inf([x])
        in_list = x in [x]

        success = result == x and in_list
        print(f"[{x}] -> result={result}, x in list={in_list}, success={success}")

    return True

def test_inductive_step_structure():
    """Test the inductive step structure for x::xs cases"""
    print("\n=== Testing Inductive Step Structure ===")

    test_cases = [
        ([1, 2], "x=1 < tail_max=2, result should be 2"),
        ([2, 1], "x=2 > tail_max=1, result should be 2"),
        ([1, 2, 3], "x=1 < tail_max=3, result should be 3"),
        ([3, 2, 1], "x=3 > tail_max=2, result should be 3"),
        ([5, 1, 2, 4], "x=5 > tail_max=4, result should be 5"),
        ([-1, -2, -3], "x=-1 > tail_max=-2, result should be -1"),
    ]

    for xs, description in test_cases:
        if len(xs) < 2:
            continue

        x = xs[0]
        tail = xs[1:]

        tail_result = fold_right_max_inf(tail)
        full_result = fold_right_max_inf(xs)

        # Check which element won the max operation
        if isinstance(tail_result, NegInf):
            expected = x
            winner = "x (tail is NegInf)"
        else:
            expected = max(x, tail_result)
            winner = "x" if expected == x else f"tail_result({tail_result})"

        result_in_list = (not isinstance(full_result, NegInf)) and (full_result in xs)

        print(f"{xs}: {description}")
        print(f"  x={x}, tail_result={tail_result}, full_result={full_result}")
        print(f"  expected={expected}, winner={winner}")
        print(f"  result_in_list={result_in_list}")
        print()

    return True

def test_membership_preservation():
    """
    Key insight: In the inductive step x::xs, fold_right gives max(x, fold_right(xs)).
    - If max = x, then x ∈ x::xs ✓
    - If max = fold_right(xs), then by IH fold_right(xs) ∈ xs, so it's also ∈ x::xs ✓
    """
    print("=== Testing Membership Preservation Property ===")

    test_cases = []

    # Add systematic test cases
    for _ in range(30):
        size = random.randint(2, 6)
        xs = [random.randint(-20, 20) for _ in range(size)]
        test_cases.append(xs)

    failures = 0
    total = 0

    for xs in test_cases:
        if len(xs) < 2:
            continue

        total += 1
        x = xs[0]
        tail = xs[1:]

        # Get results
        tail_result = fold_right_max_inf(tail)
        full_result = fold_right_max_inf(xs)

        # Verify tail_result ∈ tail (assuming IH holds)
        tail_membership = isinstance(tail_result, NegInf) or (tail_result in tail)

        # Verify full_result ∈ xs
        full_membership = (not isinstance(full_result, NegInf)) and (full_result in xs)

        # Check the max logic
        if isinstance(tail_result, NegInf):
            expected_full = x
        else:
            expected_full = max(x, tail_result)

        correct_max = full_result == expected_full

        if not (tail_membership and full_membership and correct_max):
            failures += 1
            print(f"FAIL: xs={xs}")
            print(f"  tail_result={tail_result}, tail_membership={tail_membership}")
            print(f"  full_result={full_result}, full_membership={full_membership}")
            print(f"  expected_full={expected_full}, correct_max={correct_max}")
        else:
            print(f"PASS: xs={xs}, result={full_result} ∈ xs")

    print(f"\nMembership preservation: {total - failures}/{total} tests passed")
    return failures == 0

def test_proof_by_strong_induction_insight():
    """
    Test the key insight: we can prove this by strong induction on list length.
    Base: length 1 - trivial
    Step: length n+1 - use max preservation property
    """
    print("\n=== Testing Strong Induction Strategy ===")

    # Group test cases by length
    by_length = {}

    for length in range(1, 6):
        by_length[length] = []
        for _ in range(10):
            xs = [random.randint(-10, 10) for _ in range(length)]
            by_length[length].append(xs)

    for length in sorted(by_length.keys()):
        print(f"\nLength {length}:")

        failures = 0
        total = 0

        for xs in by_length[length]:
            total += 1
            result = fold_right_max_inf(xs)

            # Check membership
            membership = (not isinstance(result, NegInf)) and (result in xs)

            if not membership:
                failures += 1
                print(f"  FAIL: xs={xs}, result={result}")
            else:
                print(f"  PASS: xs={xs}, result={result}")

        print(f"  Length {length}: {total - failures}/{total} passed")

    return True

if __name__ == "__main__":
    print("Analyzing fold_right_max_inf_in lemma structure for proof strategy")
    print("=" * 70)

    test_base_case()
    test_inductive_step_structure()
    success = test_membership_preservation()
    test_proof_by_strong_induction_insight()

    print("\n" + "=" * 70)
    print("PROOF STRATEGY INSIGHTS:")
    print("1. Base case [x]: trivial - fold_right gives x, and x ∈ [x]")
    print("2. Inductive step x::xs: fold_right gives max(x, fold_right(xs))")
    print("   - If result = x, then x ∈ x::xs ✓")
    print("   - If result = fold_right(xs), then by IH it's in xs, so it's in x::xs ✓")
    print("3. Key lemma needed: max(x, y) ∈ {x} ∪ S when y ∈ S")
    print("4. This should be provable by straightforward induction on list structure")

    if success:
        print("\n✅ All structural tests pass - proof strategy is sound!")
    else:
        print("\n❌ Some structural tests failed - need to revise strategy")