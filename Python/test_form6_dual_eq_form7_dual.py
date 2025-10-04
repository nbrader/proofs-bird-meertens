#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def fold_left(f, xs, init):
    """Standard fold_left"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def inits_rec(xs):
    """inits_rec function that produces all prefixes"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def nonNegMaximum_dual(xs):
    """nonNegMaximum_dual: fold_left max xs 0"""
    return fold_left(max, xs, 0)

def form6_dual(xs):
    """form6_dual: nonNegMaximum_dual (map (fold_left nonNegPlus prefix 0) (inits_rec xs))"""
    prefixes = inits_rec(xs)
    prefix_sums = [fold_left(nonNegPlus, prefix, 0) for prefix in prefixes]
    return nonNegMaximum_dual(prefix_sums)

def form7_dual_corrected(xs):
    """Corrected form7_dual: Z.max 0 (fold_left nonNegPlus xs 0)"""
    fold_sum = fold_left(nonNegPlus, xs, 0)
    return max(0, fold_sum)

def test_form6_dual_eq_form7_dual(xs):
    """Test if form6_dual equals corrected form7_dual"""
    form6_result = form6_dual(xs)
    form7_result = form7_dual_corrected(xs)
    return form6_result, form7_result

def run_tests():
    """Run various test cases for the form6_dual = form7_dual theorem"""
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

    print("Testing form6_dual = form7_dual theorem:")
    print("=" * 50)

    all_passed = True
    for xs, desc in test_cases:
        form6_result, form7_result = test_form6_dual_eq_form7_dual(xs)

        passed = form6_result == form7_result
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs = {xs}")
        print(f"  form6_dual result = {form6_result}")
        print(f"  form7_dual result = {form7_result}")

        if not passed:
            all_passed = False
            print(f"  ERROR: {form6_result} != {form7_result}")

            # Debug info
            prefixes = inits_rec(xs)
            prefix_sums = [fold_left(nonNegPlus, prefix, 0) for prefix in prefixes]
            print(f"  Debug: prefixes = {prefixes}")
            print(f"  Debug: prefix sums = {prefix_sums}")
            print(f"  Debug: max of prefix sums = {max(prefix_sums) if prefix_sums else 0}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! The form6_dual = form7_dual theorem appears to be TRUE.")
    else:
        print("❌ Some tests failed. The form6_dual = form7_dual theorem might be FALSE.")

if __name__ == "__main__":
    run_tests()