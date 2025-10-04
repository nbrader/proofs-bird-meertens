#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def maxSoFarAndPreviousSum_dual(uv, x):
    """maxSoFarAndPreviousSum_dual function"""
    u, v = uv
    w = nonNegPlus(v, x)  # v <#> x
    return (max(u, w), w)  # (u <|> w, w)

def fold_left(f, xs, init):
    """Standard fold_left"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def form7_dual_corrected(xs):
    """Corrected form7_dual: Z.max 0 (fold_left nonNegPlus xs 0)"""
    fold_sum = fold_left(nonNegPlus, xs, 0)
    return max(0, fold_sum)

def form8_dual(xs):
    """form8_dual: fst (fold_left maxSoFarAndPreviousSum_dual xs (0, 0))"""
    result = fold_left(maxSoFarAndPreviousSum_dual, xs, (0, 0))
    return result[0]  # fst

def test_corrected_form7_dual_eq_form8_dual(xs):
    """Test if corrected form7_dual equals form8_dual"""
    form7_result = form7_dual_corrected(xs)
    form8_result = form8_dual(xs)
    return form7_result, form8_result

def run_tests():
    """Run various test cases for the corrected form7_dual = form8_dual theorem"""
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

    print("Testing corrected form7_dual = form8_dual theorem:")
    print("=" * 60)

    all_passed = True
    for xs, desc in test_cases:
        form7_result, form8_result = test_corrected_form7_dual_eq_form8_dual(xs)

        passed = form7_result == form8_result
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs = {xs}")
        print(f"  corrected form7_dual result = {form7_result}")
        print(f"  form8_dual result = {form8_result}")

        if not passed:
            all_passed = False
            print(f"  ERROR: {form7_result} != {form8_result}")

            # Debug info
            fold_sum = fold_left(nonNegPlus, xs, 0)
            print(f"  Debug: fold_left nonNegPlus result = {fold_sum}")

            # Show step-by-step fold_left for form8_dual
            acc = (0, 0)
            print(f"  Debug form8_dual steps: start with {acc}")
            for i, x in enumerate(xs):
                acc = maxSoFarAndPreviousSum_dual(acc, x)
                print(f"    step {i+1}: x={x} -> {acc}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! The corrected form7_dual = form8_dual theorem appears to be TRUE.")
    else:
        print("❌ Some tests failed. The corrected form7_dual = form8_dual theorem might be FALSE.")

if __name__ == "__main__":
    run_tests()