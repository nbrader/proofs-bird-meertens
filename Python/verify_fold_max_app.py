#!/usr/bin/env python3
"""
Verify that fold_left Z.max distributes over concatenation.
This tests the lemma fold_max_app_dual from Lemmas.v
"""

def fold_left_max(lst, init=0):
    """Simulate Coq's fold_left Z.max"""
    result = init
    for x in lst:
        result = max(result, x)
    return result

def test_fold_max_app_dual():
    """Test that fold_left Z.max (l1 ++ l2) 0 = Z.max (fold_left Z.max l1 0) (fold_left Z.max l2 0)"""

    test_cases = [
        ([], []),
        ([1], []),
        ([], [2]),
        ([1], [2]),
        ([1, 2], [3]),
        ([1], [2, 3]),
        ([1, 2], [3, 4]),
        ([-1, 0], [1, 2]),
        ([-5, -3], [-2, -1]),
        ([10, 5], [3, 8]),
        ([0, 0, 0], [0, 0]),
        ([-10, -5, -1], [-100, -50]),
        ([x for x in range(10)], [x for x in range(10, 20)]),
    ]

    print("Testing fold_max_app_dual: fold_left Z.max (l1 ++ l2) 0 = Z.max (fold_left Z.max l1 0) (fold_left Z.max l2 0)")
    print("=" * 100)

    passed = 0
    total = 0

    for i, (l1, l2) in enumerate(test_cases):
        # Left side: fold_left Z.max (l1 ++ l2) 0
        left = fold_left_max(l1 + l2, 0)

        # Right side: Z.max (fold_left Z.max l1 0) (fold_left Z.max l2 0)
        fold_l1 = fold_left_max(l1, 0)
        fold_l2 = fold_left_max(l2, 0)
        right = max(fold_l1, fold_l2)

        is_equal = left == right
        total += 1

        if is_equal:
            passed += 1
            status = "✓ PASS"
        else:
            status = "✗ FAIL"

        print(f"Test {i+1:2d}: {status} | l1={l1} l2={l2}")
        print(f"         Left:  fold_left max ({l1 + l2}) 0 = {left}")
        print(f"         Right: max({fold_l1}, {fold_l2}) = {right}")

        if not is_equal:
            print(f"         FAILURE: Expected {right}, got {left}")
        print()

    print("=" * 100)
    print(f"Results: {passed}/{total} tests passed")

    if passed == total:
        print("✓ LEMMA IS TRUE: fold_left Z.max distributes over concatenation")
        return True
    else:
        print("✗ LEMMA IS FALSE: Found counterexample(s)")
        return False

def analyze_fold_concatenation():
    """Analyze specific examples to understand the behavior"""
    print("Analyzing fold_left max concatenation behavior:")
    print("-" * 60)

    examples = [
        ([1, 2], [3]),
        ([3], [1, 2]),
        ([1, 5], [2, 3]),
        ([-1, 0], [1, 2]),
    ]

    for l1, l2 in examples:
        print(f"\nl1 = {l1}, l2 = {l2}")

        # Step by step for l1 ++ l2
        combined = l1 + l2
        print(f"  l1 ++ l2 = {combined}")

        acc = 0
        steps = [f"init: {acc}"]
        for x in combined:
            acc = max(acc, x)
            steps.append(f"max(prev, {x}) = {acc}")
        print(f"  fold_left max: {' -> '.join(steps)}")

        # Individual folds
        fold_l1 = fold_left_max(l1, 0)
        fold_l2 = fold_left_max(l2, 0)
        print(f"  fold_left max l1 0 = {fold_l1}")
        print(f"  fold_left max l2 0 = {fold_l2}")
        print(f"  max({fold_l1}, {fold_l2}) = {max(fold_l1, fold_l2)}")

        is_equal = acc == max(fold_l1, fold_l2)
        print(f"  Equal? {is_equal}")

if __name__ == "__main__":
    is_true = test_fold_max_app_dual()
    analyze_fold_concatenation()

    print("\nConclusion:")
    if is_true:
        print("The lemma fold_max_app_dual is TRUE and should be provable.")
        print("This is because fold_left max effectively finds the maximum of all elements,")
        print("and max(max_of_l1, max_of_l2) = max_of_combined when starting from 0.")
    else:
        print("The lemma fold_max_app_dual is FALSE and should not be provable.")