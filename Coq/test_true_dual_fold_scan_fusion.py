#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def fold_left_pair_fn(uv, x):
    """The pair function from the LHS of the lemma"""
    u, v = uv
    new_v = nonNegPlus(v, x)
    new_u = max(u, new_v)
    return (new_u, new_v)

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

def test_true_dual_fold_scan_fusion(xs):
    """Test the true dual fold_scan_fusion_pair_dual lemma with u0=0, v0=0"""

    # LHS: fold_left with pair function starting from (0, 0)
    lhs = fold_left(fold_left_pair_fn, xs, (0, 0))

    # RHS: (fold_left Z.max (scan_left nonNegPlus xs 0) 0, fold_left nonNegPlus xs 0)
    scan_result = scan_left(nonNegPlus, xs, 0)
    rhs_first = fold_left(max, scan_result, 0)
    rhs_second = fold_left(nonNegPlus, xs, 0)
    rhs = (rhs_first, rhs_second)

    return lhs, rhs, scan_result

def run_tests():
    """Run various test cases for the true dual fold_scan_fusion_pair_dual lemma"""
    test_cases = [
        ([1, 2], "Two positives"),
        ([1, 2, 3], "Three positives"),
        ([-1], "Single negative"),
        ([-1, -2], "Two negatives"),
        ([2, -1, 3], "Mixed values"),
        ([1, -3, 2], "Positive, large negative, positive"),
        ([0, 0, 0], "All zeros"),
        ([1, 1, 1], "All ones"),
        ([-5, 10, -3, 8], "Complex mixed"),
        ([], "Empty list"),
    ]

    print("Testing true dual fold_scan_fusion_pair_dual lemma (u0=0, v0=0):")
    print("=" * 70)

    all_passed = True
    for xs, desc in test_cases:
        lhs, rhs, scan_result = test_true_dual_fold_scan_fusion(xs)

        passed = lhs == rhs
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs = {xs}")
        print(f"  scan_left result = {scan_result}")
        print(f"  LHS = {lhs}")
        print(f"  RHS = {rhs}")

        if not passed:
            all_passed = False
            print(f"  ERROR: {lhs} != {rhs}")

            # Debug: show step-by-step fold_left for LHS
            acc = (0, 0)
            print(f"  Debug LHS steps: start with {acc}")
            for i, x in enumerate(xs):
                acc = fold_left_pair_fn(acc, x)
                print(f"    step {i+1}: x={x} -> {acc}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! The true dual fold_scan_fusion_pair_dual lemma appears to be TRUE.")
    else:
        print("❌ Some tests failed. The true dual fold_scan_fusion_pair_dual lemma might be FALSE.")

if __name__ == "__main__":
    run_tests()