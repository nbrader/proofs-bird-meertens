#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def scan_left(f, xs, init):
    """scan_left function that produces intermediate results"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result[:-1]  # Remove the last element to match Coq's scan_left

def fold_left(f, xs, init):
    """Standard fold_left"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def test_scan_fold_max_equiv_from_zero(xs):
    """Test the scan_fold_max_equiv_from_zero lemma"""

    # LHS: fold_left Z.max (scan_left (fun acc x => nonNegPlus acc x) xs 0) 0
    scan_result = scan_left(nonNegPlus, xs, 0)
    lhs = fold_left(max, scan_result, 0)

    # RHS: Z.max 0 (fold_left (fun acc x => nonNegPlus acc x) xs 0)
    fold_result = fold_left(nonNegPlus, xs, 0)
    rhs = max(0, fold_result)

    return lhs, rhs, scan_result, fold_result

def run_tests():
    """Run various test cases for the scan_fold_max_equiv_from_zero lemma"""
    test_cases = [
        ([], "Empty list"),
        ([1], "Single positive"),
        ([1, 2], "Two positives"),
        ([1, 2, 3], "Three positives"),
        ([-1], "Single negative"),
        ([-1, -2], "Two negatives"),
        ([2, -1, 3], "Mixed values"),
        ([1, -3, 2], "Positive, large negative, positive"),
        ([0, 0, 0], "All zeros"),
        ([1, 1, 1], "All ones"),
        ([-5, 10, -3, 8], "Complex mixed"),
    ]

    print("Testing scan_fold_max_equiv_from_zero lemma:")
    print("=" * 60)

    all_passed = True
    for xs, desc in test_cases:
        lhs, rhs, scan_result, fold_result = test_scan_fold_max_equiv_from_zero(xs)

        passed = lhs == rhs
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs = {xs}")
        print(f"  scan_left result = {scan_result}")
        print(f"  fold_left result = {fold_result}")
        print(f"  LHS (fold_left max scan 0) = {lhs}")
        print(f"  RHS (max 0 fold_result) = {rhs}")

        if not passed:
            all_passed = False
            print(f"  ERROR: {lhs} != {rhs}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! The scan_fold_max_equiv_from_zero lemma appears to be TRUE.")
    else:
        print("❌ Some tests failed. The scan_fold_max_equiv_from_zero lemma might be FALSE.")

if __name__ == "__main__":
    run_tests()