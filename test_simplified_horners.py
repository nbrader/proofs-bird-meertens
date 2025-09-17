#!/usr/bin/env python3
"""
Test the simplified version of generalised_horners_rule.

Since tropical_horner_op(x, y) = nonNegPlus(x, y), the lemma becomes:
fold_right nonNegPlus 0 = nonNegMaximum ∘ map nonNegSum ∘ inits
"""

def nonNegPlus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def z_max(x, y):
    """Z.max operation"""
    return max(x, y)

def fold_right(op, init, xs):
    """fold_right operation"""
    if not xs:
        return init
    return op(xs[0], fold_right(op, init, xs[1:]))

def nonNegSum(xs):
    """nonNegSum: fold_right nonNegPlus 0 xs"""
    return fold_right(nonNegPlus, 0, xs)

def nonNegMaximum(xs):
    """nonNegMaximum: fold_right Z.max 0 xs"""
    return fold_right(z_max, 0, xs)

def inits(xs):
    """Return all initial segments of xs, including empty list"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def lhs_simplified(xs):
    """Left side: fold_right nonNegPlus 0"""
    return fold_right(nonNegPlus, 0, xs)

def rhs(xs):
    """Right side: nonNegMaximum ∘ map nonNegSum ∘ inits"""
    inits_xs = inits(xs)
    mapped = [nonNegSum(seg) for seg in inits_xs]
    return nonNegMaximum(mapped)

def debug_case(xs):
    """Debug a specific case"""
    print(f"Case: {xs}")

    # LHS
    left = lhs_simplified(xs)
    print(f"LHS: fold_right nonNegPlus 0 {xs} = {left}")

    # RHS step by step
    inits_xs = inits(xs)
    print(f"inits({xs}) = {inits_xs}")

    mapped = []
    for seg in inits_xs:
        seg_sum = nonNegSum(seg)
        mapped.append(seg_sum)
        print(f"  nonNegSum({seg}) = {seg_sum}")

    right = nonNegMaximum(mapped)
    print(f"nonNegMaximum({mapped}) = {right}")

    print(f"Equal: {left == right}")
    print()

    return left == right

def test_cases():
    """Test the simplified version"""
    test_lists = [
        [],
        [1],
        [-1],
        [1, 2],
        [1, -1],
        [-1, 1],
        [1, 2, 3],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -3, 2],
    ]

    print("Testing SIMPLIFIED generalised_horners_rule:")
    print("fold_right nonNegPlus 0 = nonNegMaximum ∘ map nonNegSum ∘ inits")
    print()

    passed = 0
    failed = 0

    for xs in test_lists:
        if debug_case(xs):
            passed += 1
        else:
            failed += 1

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("All tests passed! The simplified lemma is TRUE.")
    else:
        print("Some tests failed! The simplified lemma is FALSE.")