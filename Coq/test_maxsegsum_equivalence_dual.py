#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def nonNegSum_dual(xs):
    """nonNegSum_dual: fold_left nonNegPlus xs 0"""
    acc = 0
    for x in xs:
        acc = nonNegPlus(acc, x)
    return acc

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

def maxSoFarAndPreviousSum_dual(uv, x):
    """maxSoFarAndPreviousSum_dual function"""
    u, v = uv
    w = nonNegPlus(v, x)  # v <#> x
    return (max(u, w), w)  # (u <|> w, w)

def segs_dual(xs):
    """segs_dual: all contiguous subsequences"""
    result = []
    for i in range(len(xs)):
        for j in range(i, len(xs) + 1):
            result.append(xs[i:j])
    return result

def form1_dual(xs):
    """form1_dual: nonNegMaximum_dual ∘ map nonNegSum_dual ∘ segs_dual"""
    segments = segs_dual(xs)
    segment_sums = [nonNegSum_dual(seg) for seg in segments]
    return nonNegMaximum_dual(segment_sums)

def form8_dual(xs):
    """form8_dual: fst (fold_left maxSoFarAndPreviousSum_dual xs (0, 0))"""
    result = fold_left(maxSoFarAndPreviousSum_dual, xs, (0, 0))
    return result[0]  # fst

def test_maxsegsum_equivalence_dual():
    """Comprehensive test of MaxSegSum_Equivalence_Dual: form1_dual = form8_dual"""

    # More comprehensive test cases
    test_cases = [
        ([], "Empty list"),
        ([1], "Single positive"),
        ([-1], "Single negative"),
        ([0], "Single zero"),
        ([1, 2], "Two positives"),
        ([-1, -2], "Two negatives"),
        ([1, -1], "Positive then negative"),
        ([-1, 1], "Negative then positive"),
        ([1, 2, 3], "Three positives"),
        ([-1, -2, -3], "Three negatives"),
        ([1, -3, 2], "Positive, large negative, positive"),
        ([2, -1, 3], "Mixed values"),
        ([0, 0, 0], "All zeros"),
        ([1, 1, 1], "All ones"),
        ([-1, -1, -1], "All negative ones"),
        ([5, -10, 3, 7], "Large changes"),
        ([-5, 10, -3, 8], "Complex mixed"),
        ([1, -2, 1, -2, 1], "Alternating"),
        ([10, -5, -3, 8, -2, 6], "Longer mixed sequence"),
        (list(range(1, 11)), "Ascending 1..10"),
        (list(range(-5, 6)), "Range -5..5"),
    ]

    print("Comprehensive test of MaxSegSum_Equivalence_Dual:")
    print("form1_dual = form8_dual")
    print("=" * 60)

    all_passed = True
    failed_cases = []

    for xs, desc in test_cases:
        f1 = form1_dual(xs)
        f8 = form8_dual(xs)

        passed = f1 == f8
        status = "PASS" if passed else "FAIL"

        if not passed:
            all_passed = False
            failed_cases.append((xs, desc, f1, f8))
            print(f"{status}: {desc}")
            print(f"  xs = {xs}")
            print(f"  form1_dual = {f1}")
            print(f"  form8_dual = {f8}")
            print(f"  ERROR: {f1} != {f8}")

            # Debug: show segments and their sums for form1_dual
            segments = segs_dual(xs)
            segment_sums = [nonNegSum_dual(seg) for seg in segments]
            print(f"  Debug form1_dual:")
            print(f"    segments = {segments}")
            print(f"    segment_sums = {segment_sums}")
            print(f"    max = {nonNegMaximum_dual(segment_sums)}")

            # Debug: show step-by-step for form8_dual
            acc = (0, 0)
            print(f"  Debug form8_dual: start with {acc}")
            for i, x in enumerate(xs):
                acc = maxSoFarAndPreviousSum_dual(acc, x)
                print(f"    step {i+1}: x={x} -> {acc}")
            print()
        else:
            print(f"{status}: {desc} - form1_dual=form8_dual={f1}")

    print()
    if all_passed:
        print("🎉 ALL TESTS PASSED!")
        print("MaxSegSum_Equivalence_Dual (form1_dual = form8_dual) appears to be TRUE.")
        return True
    else:
        print(f"❌ {len(failed_cases)} tests failed.")
        print("MaxSegSum_Equivalence_Dual (form1_dual = form8_dual) is FALSE.")
        print()
        print("Failed cases summary:")
        for xs, desc, f1, f8 in failed_cases:
            print(f"  {desc}: xs={xs}, form1_dual={f1}, form8_dual={f8}")
        return False

if __name__ == "__main__":
    test_maxsegsum_equivalence_dual()