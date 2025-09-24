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

def scan_left(f, xs, init):
    """scan_left function that produces intermediate results"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result[:-1]  # Remove the last element to match Coq's scan_left

def inits_rec(xs):
    """inits_rec function that produces all prefixes"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def tails(xs):
    """tails function that produces all suffixes"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[i:])
    return result

def maxSoFarAndPreviousSum_dual(uv, x):
    """maxSoFarAndPreviousSum_dual function"""
    u, v = uv
    w = nonNegPlus(v, x)  # v <#> x
    return (max(u, w), w)  # (u <|> w, w)

def segs_dual(xs):
    """segs_dual: all subsequences (dual version)"""
    # This is likely the same as segs since segs should be its own dual
    # For now, implementing as all contiguous subsequences
    result = []
    for i in range(len(xs)):
        for j in range(i, len(xs) + 1):
            result.append(xs[i:j])
    return result

# Define all dual forms
def form1_dual(xs):
    """form1_dual: nonNegMaximum_dual ∘ map nonNegSum_dual ∘ segs_dual"""
    segments = segs_dual(xs)
    segment_sums = [nonNegSum_dual(seg) for seg in segments]
    return nonNegMaximum_dual(segment_sums)

def form2_dual(xs):
    """form2_dual: nonNegMaximum_dual ∘ map nonNegSum_dual ∘ concat ∘ map tails ∘ inits_rec"""
    prefixes = inits_rec(xs)
    all_suffixes = []
    for prefix in prefixes:
        all_suffixes.extend(tails(prefix))
    segment_sums = [nonNegSum_dual(seg) for seg in all_suffixes]
    return nonNegMaximum_dual(segment_sums)

def form6_dual(xs):
    """form6_dual: nonNegMaximum_dual ∘ map (fold_left nonNegPlus prefix 0) ∘ inits_rec"""
    prefixes = inits_rec(xs)
    prefix_sums = [fold_left(nonNegPlus, prefix, 0) for prefix in prefixes]
    return nonNegMaximum_dual(prefix_sums)

def form7_dual(xs):
    """form7_dual: nonNegMaximum_dual (scan_left nonNegPlus xs 0)"""
    scan_result = scan_left(nonNegPlus, xs, 0)
    return nonNegMaximum_dual(scan_result)

def form8_dual(xs):
    """form8_dual: fst (fold_left maxSoFarAndPreviousSum_dual xs (0, 0))"""
    result = fold_left(maxSoFarAndPreviousSum_dual, xs, (0, 0))
    return result[0]  # fst

def test_dual_equivalences():
    """Test various dual form equivalences"""
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

    print("Testing dual form equivalences:")
    print("=" * 60)

    # Test form1_dual = form2_dual
    print("Testing form1_dual = form2_dual:")
    all_passed_12 = True
    for xs, desc in test_cases:
        f1 = form1_dual(xs)
        f2 = form2_dual(xs)
        if f1 != f2:
            all_passed_12 = False
            print(f"  FAIL {desc}: form1_dual={f1}, form2_dual={f2}")

    if all_passed_12:
        print("  ✅ ALL TESTS PASSED for form1_dual = form2_dual")
    print()

    # Test form6_dual = form7_dual
    print("Testing form6_dual = form7_dual:")
    all_passed_67 = True
    for xs, desc in test_cases:
        f6 = form6_dual(xs)
        f7 = form7_dual(xs)
        if f6 != f7:
            all_passed_67 = False
            print(f"  FAIL {desc}: form6_dual={f6}, form7_dual={f7}")

    if all_passed_67:
        print("  ✅ ALL TESTS PASSED for form6_dual = form7_dual")
    print()

    # Test form7_dual = form8_dual
    print("Testing form7_dual = form8_dual:")
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

    # Test overall equivalence chain form1_dual = form8_dual
    print("Testing overall form1_dual = form8_dual:")
    all_passed_18 = True
    for xs, desc in test_cases:
        f1 = form1_dual(xs)
        f8 = form8_dual(xs)
        if f1 != f8:
            all_passed_18 = False
            print(f"  FAIL {desc}: form1_dual={f1}, form8_dual={f8}")

    if all_passed_18:
        print("  ✅ ALL TESTS PASSED for form1_dual = form8_dual")
    else:
        print("  ❌ FAILED: The overall dual equivalence is FALSE")

if __name__ == "__main__":
    test_dual_equivalences()