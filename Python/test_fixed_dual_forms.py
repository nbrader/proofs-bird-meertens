#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def nonNegMaximum_dual(xs):
    """nonNegMaximum_dual: fold_left max xs 0"""
    if not xs:
        return 0
    acc = 0
    for x in xs:
        acc = max(acc, x)
    return acc

def fold_left(f, xs, init):
    """Standard fold_left"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def scan_left_correct(f, xs, init):
    """CORRECT scan_left: includes init and all intermediate results"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def inits_rec(xs):
    """inits_rec function that produces all prefixes"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def maxSoFarAndPreviousSum_dual(uv, x):
    """maxSoFarAndPreviousSum_dual function"""
    u, v = uv
    w = nonNegPlus(v, x)  # v <#> x
    return (max(u, w), w)  # (u <|> w, w)

def form6_dual(xs):
    """form6_dual: nonNegMaximum_dual ∘ map (fold_left nonNegPlus prefix 0) ∘ inits_rec"""
    prefixes = inits_rec(xs)
    prefix_sums = [fold_left(nonNegPlus, prefix, 0) for prefix in prefixes]
    return nonNegMaximum_dual(prefix_sums)

def form7_dual(xs):
    """form7_dual: nonNegMaximum_dual (scan_left nonNegPlus xs 0) - CORRECTED"""
    scan_result = scan_left_correct(nonNegPlus, xs, 0)
    return nonNegMaximum_dual(scan_result)

def form8_dual(xs):
    """form8_dual: fst (fold_left maxSoFarAndPreviousSum_dual xs (0, 0))"""
    result = fold_left(maxSoFarAndPreviousSum_dual, xs, (0, 0))
    return result[0]  # fst

def test_corrected_dual_equivalences():
    """Test dual equivalences with corrected scan_left implementation"""
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

    print("Testing CORRECTED dual form equivalences:")
    print("=" * 60)

    # Test form6_dual = form7_dual with correct scan_left
    print("Testing form6_dual = form7_dual (with corrected scan_left):")
    all_passed_67 = True
    for xs, desc in test_cases:
        f6 = form6_dual(xs)
        f7 = form7_dual(xs)
        if f6 != f7:
            all_passed_67 = False
            print(f"  FAIL {desc}: form6_dual={f6}, form7_dual={f7}")

            # Debug info
            prefixes = inits_rec(xs)
            prefix_sums = [fold_left(nonNegPlus, prefix, 0) for prefix in prefixes]
            scan_result = scan_left_correct(nonNegPlus, xs, 0)

            print(f"    Debug: prefixes = {prefixes}")
            print(f"    Debug: prefix_sums = {prefix_sums}")
            print(f"    Debug: scan_result = {scan_result}")
            print(f"    Debug: scan_result == prefix_sums: {scan_result == prefix_sums}")

    if all_passed_67:
        print("  ✅ ALL TESTS PASSED for form6_dual = form7_dual")
    print()

    # Test form7_dual = form8_dual with correct scan_left
    print("Testing form7_dual = form8_dual (with corrected scan_left):")
    all_passed_78 = True
    for xs, desc in test_cases:
        f7 = form7_dual(xs)
        f8 = form8_dual(xs)
        if f7 != f8:
            all_passed_78 = False
            print(f"  FAIL {desc}: form7_dual={f7}, form8_dual={f8}")

    if all_passed_78:
        print("  ✅ ALL TESTS PASSED for form7_dual = form8_dual")
    print()

    # Test overall equivalence
    print("Testing overall form6_dual = form8_dual:")
    all_passed_68 = True
    for xs, desc in test_cases:
        f6 = form6_dual(xs)
        f8 = form8_dual(xs)
        if f6 != f8:
            all_passed_68 = False
            print(f"  FAIL {desc}: form6_dual={f6}, form8_dual={f8}")

    if all_passed_68:
        print("  ✅ ALL TESTS PASSED for form6_dual = form8_dual")
    else:
        print("  ❌ FAILED: The form6_dual = form8_dual relationship is FALSE")

if __name__ == "__main__":
    test_corrected_dual_equivalences()