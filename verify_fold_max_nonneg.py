#!/usr/bin/env python3
"""
Verify that fold_left Z.max l 0 is always non-negative.
This tests the lemma fold_max_nonneg_dual from Lemmas.v
"""

def fold_left_max(lst, init=0):
    """Simulate Coq's fold_left Z.max"""
    result = init
    for x in lst:
        result = max(result, x)
    return result

def test_fold_max_nonneg():
    """Test that fold_left Z.max l 0 >= 0 for various lists"""

    test_cases = [
        [],  # empty list
        [0],  # single zero
        [1],  # single positive
        [-1],  # single negative
        [0, 0, 0],  # all zeros
        [1, 2, 3],  # all positive
        [-3, -2, -1],  # all negative
        [-5, 0, 3],  # mixed
        [-10, -5, -1],  # all negative, decreasing
        [5, -10, 3, -1],  # mixed positive/negative
        [x for x in range(-100, 101)],  # large range
        [-1000, -500, -100, -50, -10, -1],  # all negative
    ]

    print("Testing fold_max_nonneg_dual: 0 <= fold_left Z.max l 0")
    print("=" * 60)

    passed = 0
    total = 0

    for i, lst in enumerate(test_cases):
        result = fold_left_max(lst, 0)
        is_nonneg = result >= 0
        total += 1

        if is_nonneg:
            passed += 1
            status = "✓ PASS"
        else:
            status = "✗ FAIL"

        print(f"Test {i+1:2d}: {status} | List: {lst[:10]}{'...' if len(lst) > 10 else ''} | Result: {result}")

        if not is_nonneg:
            print(f"         FAILURE: Expected >= 0, got {result}")

    print("=" * 60)
    print(f"Results: {passed}/{total} tests passed")

    if passed == total:
        print("✓ LEMMA IS TRUE: fold_left Z.max l 0 is always non-negative")
        return True
    else:
        print("✗ LEMMA IS FALSE: Found counterexample(s)")
        return False

def analyze_fold_behavior():
    """Analyze how fold_left max behaves to understand the proof strategy"""
    print("\nAnalyzing fold_left max behavior:")
    print("-" * 40)

    examples = [
        [],
        [5],
        [-3],
        [1, 2],
        [-1, -2],
        [1, -2, 3]
    ]

    for lst in examples:
        step_by_step = []
        acc = 0
        step_by_step.append(f"init: {acc}")

        for x in lst:
            acc = max(acc, x)
            step_by_step.append(f"max({acc if acc != max(acc, x) else step_by_step[-1].split(': ')[1]}, {x}) = {acc}")

        print(f"List {lst}: {' -> '.join(step_by_step)} | Final: {acc}")

if __name__ == "__main__":
    is_true = test_fold_max_nonneg()
    analyze_fold_behavior()

    print("\nConclusion:")
    if is_true:
        print("The lemma fold_max_nonneg_dual is TRUE and should be provable.")
        print("Proof strategy: Since we start with 0 and max(0, x) >= 0 for any x,")
        print("the result is always non-negative.")
    else:
        print("The lemma fold_max_nonneg_dual is FALSE and should not be provable.")