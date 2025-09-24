#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def maxSoFarAndPreviousSum_dual(uv, x):
    """maxSoFarAndPreviousSum_dual function"""
    u, v = uv
    w = nonNegPlus(v, x)  # v <#> x
    return (max(u, w), w)  # (u <|> w, w)

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

def nonNegMaximum_dual(xs):
    """nonNegMaximum_dual: fold_left max xs 0"""
    return fold_left(max, xs, 0)

def form7_dual_correct(xs):
    """Correct form7_dual: nonNegMaximum_dual (scan_left nonNegPlus xs 0)"""
    scan_result = scan_left(nonNegPlus, xs, 0)
    return nonNegMaximum_dual(scan_result)

def form8_dual(xs):
    """form8_dual: fst (fold_left maxSoFarAndPreviousSum_dual xs (0, 0))"""
    result = fold_left(maxSoFarAndPreviousSum_dual, xs, (0, 0))
    return result[0]  # fst

def test_correct_form7_dual_eq_form8_dual(xs):
    """Test if correct form7_dual equals form8_dual"""
    form7_result = form7_dual_correct(xs)
    form8_result = form8_dual(xs)
    return form7_result, form8_result

def run_tests():
    """Run various test cases for the correct form7_dual = form8_dual theorem"""
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

    print("Testing correct form7_dual = form8_dual theorem:")
    print("=" * 60)

    all_passed = True
    for xs, desc in test_cases:
        form7_result, form8_result = test_correct_form7_dual_eq_form8_dual(xs)

        passed = form7_result == form8_result
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs = {xs}")
        print(f"  correct form7_dual result = {form7_result}")
        print(f"  form8_dual result = {form8_result}")

        if not passed:
            all_passed = False
            print(f"  ERROR: {form7_result} != {form8_result}")

            # Debug info
            scan_result = scan_left(nonNegPlus, xs, 0)
            print(f"  Debug: scan_left result = {scan_result}")

            # Show step-by-step fold_left for form8_dual
            acc = (0, 0)
            print(f"  Debug form8_dual steps: start with {acc}")
            for i, x in enumerate(xs):
                acc = maxSoFarAndPreviousSum_dual(acc, x)
                print(f"    step {i+1}: x={x} -> {acc}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! The correct form7_dual = form8_dual theorem appears to be TRUE.")
    else:
        print("❌ Some tests failed. The correct form7_dual = form8_dual theorem might be FALSE.")

if __name__ == "__main__":
    run_tests()