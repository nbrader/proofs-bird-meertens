#!/usr/bin/env python3

"""
Test script to analyze if swapping tails↔inits and fold_right↔fold_left
preserves the mathematical equivalences in the Bird-Meertens formalism.

This script implements both the original forms and their "dual" versions
to computationally verify if the transformations remain valid.
"""

def tails(xs):
    """Original tails function: returns all suffixes of xs"""
    if not xs:
        return [[]]
    return [xs[i:] for i in range(len(xs) + 1)]

def inits(xs):
    """Original inits function: returns all prefixes of xs"""
    if not xs:
        return [[]]
    return [xs[:i] for i in range(len(xs) + 1)]

def fold_right(f, init, xs):
    """fold_right f init [x1, x2, ..., xn] = f x1 (f x2 (... (f xn init)...))"""
    result = init
    for x in reversed(xs):
        result = f(x, result)
    return result

def fold_left(f, init, xs):
    """fold_left f init [x1, x2, ..., xn] = f (... (f (f init x1) x2) ...) xn"""
    result = init
    for x in xs:
        result = f(result, x)
    return result

def scan_right(f, init, xs):
    """Scan right: produces list of intermediate fold_right results"""
    if not xs:
        return [init]

    result = []
    accumulator = init
    for x in reversed(xs):
        accumulator = f(x, accumulator)
        result.append(accumulator)
    result.append(init)
    return list(reversed(result))

def scan_left(f, init, xs):
    """Scan left: produces list of intermediate fold_left results"""
    result = [init]
    accumulator = init
    for x in xs:
        accumulator = f(accumulator, x)
        result.append(accumulator)
    return result

def nonNegPlus(x, y):
    """Non-negative addition: max(0, x + y)"""
    return max(0, x + y)

def nonNegSum(xs):
    """Sum of list with non-negative constraint"""
    return fold_right(nonNegPlus, 0, xs)

def nonNegMaximum(xs):
    """Maximum of list, or 0 if empty"""
    if not xs:
        return 0
    return max(0, max(xs))

def segs(xs):
    """All contiguous segments of xs"""
    result = []
    for tail in tails(xs):
        for init in inits(tail):
            result.append(init)
    return result

def concat(xss):
    """Concatenate list of lists"""
    result = []
    for xs in xss:
        result.extend(xs)
    return result

# Original forms
def form1_original(xs):
    return nonNegMaximum([nonNegSum(seg) for seg in segs(xs)])

def form2_original(xs):
    all_inits = []
    for tail in tails(xs):
        all_inits.extend(inits(tail))
    return nonNegMaximum([nonNegSum(seg) for seg in all_inits])

def form5_original(xs):
    return nonNegMaximum([
        nonNegMaximum([nonNegSum(init) for init in inits(tail)])
        for tail in tails(xs)
    ])

def form6_original(xs):
    return nonNegMaximum([fold_right(nonNegPlus, 0, tail) for tail in tails(xs)])

def form7_original(xs):
    return nonNegMaximum(scan_right(nonNegPlus, 0, xs))

# Dual forms (swap tails↔inits, fold_right↔fold_left, scan_right↔scan_left)
def segs_dual(xs):
    """All contiguous segments using dual approach: inits of tails → tails of inits"""
    result = []
    for init in inits(xs):
        for tail in tails(init):
            result.append(tail)
    return result

def nonNegSum_dual(xs):
    """Sum using fold_left instead of fold_right"""
    return fold_left(lambda acc, x: nonNegPlus(acc, x), 0, xs)

def form1_dual(xs):
    return nonNegMaximum([nonNegSum_dual(seg) for seg in segs_dual(xs)])

def form2_dual(xs):
    all_tails = []
    for init in inits(xs):
        all_tails.extend(tails(init))
    return nonNegMaximum([nonNegSum_dual(seg) for seg in all_tails])

def form5_dual(xs):
    return nonNegMaximum([
        nonNegMaximum([nonNegSum_dual(tail) for tail in tails(init)])
        for init in inits(xs)
    ])

def form6_dual(xs):
    return nonNegMaximum([fold_left(lambda acc, x: nonNegPlus(acc, x), 0, init) for init in inits(xs)])

def form7_dual(xs):
    return nonNegMaximum(scan_left(lambda acc, x: nonNegPlus(acc, x), 0, xs))

def test_equivalences_original():
    """Test that original forms are equivalent"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -3, 5, -3, 5],
        [1, 2, 3, 4, 5]
    ]

    print("Testing original form equivalences:")
    for xs in test_cases:
        f1 = form1_original(xs)
        f2 = form2_original(xs)
        f5 = form5_original(xs)
        f6 = form6_original(xs)
        f7 = form7_original(xs)

        print(f"  {xs}: f1={f1}, f2={f2}, f5={f5}, f6={f6}, f7={f7}")

        if not (f1 == f2 == f5 == f6 == f7):
            print(f"    ERROR: Forms not equivalent for {xs}")
            return False

    print("  ✓ All original forms equivalent")
    return True

def test_equivalences_dual():
    """Test that dual forms are equivalent"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -3, 5, -3, 5],
        [1, 2, 3, 4, 5]
    ]

    print("Testing dual form equivalences:")
    for xs in test_cases:
        f1 = form1_dual(xs)
        f2 = form2_dual(xs)
        f5 = form5_dual(xs)
        f6 = form6_dual(xs)
        f7 = form7_dual(xs)

        print(f"  {xs}: f1={f1}, f2={f2}, f5={f5}, f6={f6}, f7={f7}")

        if not (f1 == f2 == f5 == f6 == f7):
            print(f"    ERROR: Dual forms not equivalent for {xs}")
            return False

    print("  ✓ All dual forms equivalent")
    return True

def test_original_vs_dual():
    """Test if original and dual forms give same results"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -3, 5, -3, 5],
        [1, 2, 3, 4, 5]
    ]

    print("Comparing original vs dual forms:")
    matches = True
    for xs in test_cases:
        orig = form1_original(xs)
        dual = form1_dual(xs)

        print(f"  {xs}: original={orig}, dual={dual}")

        if orig != dual:
            print(f"    DIFFERENCE: Original and dual give different results for {xs}")
            matches = False

    if matches:
        print("  ✓ Original and dual forms give identical results")
    else:
        print("  ✗ Original and dual forms differ")

    return matches

def analyze_scan_functions():
    """Analyze the relationship between scan_right and scan_left"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [5, -3, 5]
    ]

    print("Analyzing scan function relationships:")

    for xs in test_cases:
        sr = scan_right(nonNegPlus, 0, xs)
        sl = scan_left(lambda acc, x: nonNegPlus(acc, x), 0, xs)

        print(f"  {xs}:")
        print(f"    scan_right: {sr}")
        print(f"    scan_left:  {sl}")
        print(f"    max(scan_right): {max(sr) if sr else 0}")
        print(f"    max(scan_left):  {max(sl) if sl else 0}")

def analyze_fold_commutativity():
    """Check if nonNegPlus preserves results under fold direction swap"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [5, -3, 5],
        [-1, -2, -3]
    ]

    print("Analyzing fold direction commutativity:")

    for xs in test_cases:
        fr = fold_right(nonNegPlus, 0, xs)
        fl = fold_left(lambda acc, x: nonNegPlus(acc, x), 0, xs)

        print(f"  {xs}: fold_right={fr}, fold_left={fl}, equal={fr==fl}")

if __name__ == "__main__":
    print("=== Analysis of Dual Forms in Bird-Meertens Formalism ===\n")

    # Test original equivalences
    orig_equiv = test_equivalences_original()
    print()

    # Test dual equivalences
    dual_equiv = test_equivalences_dual()
    print()

    # Compare original vs dual
    forms_match = test_original_vs_dual()
    print()

    # Analyze scan functions
    analyze_scan_functions()
    print()

    # Analyze fold commutativity
    analyze_fold_commutativity()
    print()

    print("=== CONCLUSION ===")
    if orig_equiv and dual_equiv and forms_match:
        print("✓ SWAPPING IS VALID: All dual transformations preserve equivalences")
    else:
        print("✗ SWAPPING IS INVALID: Dual transformations break equivalences")

    print(f"Original forms equivalent: {orig_equiv}")
    print(f"Dual forms equivalent: {dual_equiv}")
    print(f"Original matches dual: {forms_match}")