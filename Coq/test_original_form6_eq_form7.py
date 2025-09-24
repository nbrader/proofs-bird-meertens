#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def fold_right(f, xs, init):
    """Standard fold_right"""
    acc = init
    for x in reversed(xs):
        acc = f(x, acc)  # Note: x is first argument in fold_right
    return acc

def nonNegMaximum(xs):
    """nonNegMaximum: fold_right max xs 0"""
    if not xs:
        return 0
    return fold_right(max, xs, 0)

def scan_right(f, xs, init):
    """scan_right function that produces intermediate results from right to left"""
    if not xs:
        return [init]

    result = []
    acc = init
    for x in reversed(xs):
        acc = f(x, acc)  # Note: x is first argument in fold_right style
        result.append(acc)
    return list(reversed(result)) + [init]

def tails_rec(xs):
    """tails_rec function that produces all suffixes"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[i:])
    return result

def form6_original(xs):
    """form6: nonNegMaximum ∘ map (fold_right nonNegPlus 0) ∘ tails_rec"""
    suffixes = tails_rec(xs)
    suffix_sums = [fold_right(nonNegPlus, suffix, 0) for suffix in suffixes]
    return nonNegMaximum(suffix_sums)

def form7_original(xs):
    """form7: nonNegMaximum ∘ scan_right nonNegPlus 0"""
    scan_result = scan_right(nonNegPlus, xs, 0)
    return nonNegMaximum(scan_result)

def test_original_form6_eq_form7():
    """Test the original form6 = form7 equivalence"""
    test_cases = [
        ([], "Empty list"),
        ([1], "Single positive"),
        ([-1], "Single negative"),
        ([1, 2], "Two positives"),
        ([-1, -2], "Two negatives"),
        ([1, -3, 2], "Positive, large negative, positive"),
        ([2, -1, 3], "Mixed values"),
        ([0, 0, 0], "All zeros"),
        ([1, 1, 1], "All ones"),
        ([-5, 10, -3, 8], "Complex mixed"),
    ]

    print("Testing original form6 = form7 equivalence:")
    print("=" * 50)

    all_passed = True
    for xs, desc in test_cases:
        f6 = form6_original(xs)
        f7 = form7_original(xs)

        passed = f6 == f7
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs = {xs}")
        print(f"  form6 = {f6}")
        print(f"  form7 = {f7}")

        if not passed:
            all_passed = False
            print(f"  ERROR: {f6} != {f7}")

            # Debug info
            suffixes = tails_rec(xs)
            suffix_sums = [fold_right(nonNegPlus, suffix, 0) for suffix in suffixes]
            scan_result = scan_right(nonNegPlus, xs, 0)

            print(f"  Debug form6:")
            print(f"    suffixes = {suffixes}")
            print(f"    suffix_sums = {suffix_sums}")
            print(f"    max = {nonNegMaximum(suffix_sums)}")
            print(f"  Debug form7:")
            print(f"    scan_right result = {scan_result}")
            print(f"    max = {nonNegMaximum(scan_result)}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! Original form6 = form7 is TRUE.")
    else:
        print("❌ Some tests failed. Original form6 = form7 might be FALSE.")

if __name__ == "__main__":
    test_original_form6_eq_form7()