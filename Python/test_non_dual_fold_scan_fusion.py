#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def fold_right_pair_fn(x, uv):
    """The pair function from the LHS of the non-dual lemma"""
    u, v = uv
    new_v = nonNegPlus(x, v)  # x <#> v (note argument order!)
    new_u = max(u, new_v)     # u <|> new_v
    return (new_u, new_v)

def scan_right(f, xs, init):
    """scan_right function that produces intermediate results from right to left"""
    result = []
    acc = init
    for x in reversed(xs):
        acc = f(x, acc)  # Note: x is first argument in fold_right style
        result.append(acc)
    return list(reversed(result)) + [init] if xs else [init]

def fold_right(f, xs, init):
    """Standard fold_right"""
    acc = init
    for x in reversed(xs):
        acc = f(x, acc)  # Note: x is first argument
    return acc

def test_non_dual_fold_scan_fusion(xs):
    """Test the non-dual fold_scan_fusion_pair lemma"""

    # LHS: fold_right with pair function starting from (0, 0)
    lhs = fold_right(fold_right_pair_fn, xs, (0, 0))

    # RHS: (fold_right Z.max (scan_right nonNegPlus 0 xs) 0, fold_right nonNegPlus xs 0)
    scan_result = scan_right(nonNegPlus, xs, 0)
    rhs_first = fold_right(max, scan_result, 0)
    rhs_second = fold_right(nonNegPlus, xs, 0)
    rhs = (rhs_first, rhs_second)

    return lhs, rhs, scan_result

def run_tests():
    """Run various test cases for the non-dual fold_scan_fusion_pair lemma"""
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

    print("Testing non-dual fold_scan_fusion_pair lemma:")
    print("=" * 60)

    all_passed = True
    for xs, desc in test_cases:
        lhs, rhs, scan_result = test_non_dual_fold_scan_fusion(xs)

        passed = lhs == rhs
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs = {xs}")
        print(f"  scan_right result = {scan_result}")
        print(f"  LHS = {lhs}")
        print(f"  RHS = {rhs}")

        if not passed:
            all_passed = False
            print(f"  ERROR: {lhs} != {rhs}")

            # Debug: show step-by-step fold_right for LHS
            acc = (0, 0)
            print(f"  Debug LHS steps: start with {acc}")
            for i, x in enumerate(reversed(xs)):
                acc = fold_right_pair_fn(x, acc)
                print(f"    step {i+1}: x={x} -> {acc}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! The non-dual fold_scan_fusion_pair lemma appears to be TRUE.")
    else:
        print("❌ Some tests failed. The non-dual fold_scan_fusion_pair lemma might be FALSE.")

if __name__ == "__main__":
    run_tests()