#!/usr/bin/env python3
"""
Test the simplified fold_right_nonNegPlus_eq_max_prefixes lemma:
nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))

This should be equivalent to our previous version since nonNegSum = fold_right nonNegPlus 0.
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

def test_simplified_lemma(xs):
    """Test: nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))"""

    # LHS: nonNegSum xs
    lhs = nonNegSum(xs)

    # RHS: nonNegMaximum (map nonNegSum (inits xs))
    inits_xs = inits(xs)
    mapped = [nonNegSum(seg) for seg in inits_xs]
    rhs = nonNegMaximum(mapped)

    print(f"xs = {xs}")
    print(f"  LHS: nonNegSum({xs}) = {lhs}")
    print(f"  inits({xs}) = {inits_xs}")
    print(f"  map nonNegSum = {mapped}")
    print(f"  RHS: nonNegMaximum({mapped}) = {rhs}")
    print(f"  Equal: {lhs == rhs}")
    print()

    return lhs == rhs

def test_cases():
    """Test various cases"""
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

    print("Testing simplified lemma:")
    print("nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))")
    print()

    passed = 0
    failed = 0

    for xs in test_lists:
        if test_simplified_lemma(xs):
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