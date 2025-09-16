#!/usr/bin/env python3
"""
Test generalised_horners_rule' lemma:
nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec = nonNegMaximum ∘ map nonNegSum ∘ tails_rec

This says that applying the first generalised_horners_rule to each tail, then taking the maximum,
equals just taking nonNegSum of each tail, then taking the maximum.
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

def tails_rec(xs):
    """Recursive definition of tails"""
    if not xs:
        return [[]]
    return [xs] + tails_rec(xs[1:])

def lhs(xs):
    """LHS: nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec"""
    tails_xs = tails_rec(xs)
    mapped = []
    for tail in tails_xs:
        inits_tail = inits(tail)
        mapped_tail = [nonNegSum(seg) for seg in inits_tail]
        max_tail = nonNegMaximum(mapped_tail)
        mapped.append(max_tail)
    return nonNegMaximum(mapped)

def rhs(xs):
    """RHS: nonNegMaximum ∘ map nonNegSum ∘ tails_rec"""
    tails_xs = tails_rec(xs)
    mapped = [nonNegSum(tail) for tail in tails_xs]
    return nonNegMaximum(mapped)

def test_equality(xs):
    """Test if lhs(xs) == rhs(xs)"""
    left = lhs(xs)
    right = rhs(xs)
    return left == right, left, right

def debug_case(xs):
    """Debug a specific case in detail"""
    print(f"Case: {xs}")

    tails_xs = tails_rec(xs)
    print(f"tails_rec({xs}) = {tails_xs}")

    # LHS calculation
    print("LHS calculation:")
    lhs_mapped = []
    for i, tail in enumerate(tails_xs):
        inits_tail = inits(tail)
        mapped_tail = [nonNegSum(seg) for seg in inits_tail]
        max_tail = nonNegMaximum(mapped_tail)
        lhs_mapped.append(max_tail)
        print(f"  tail {i}: {tail}")
        print(f"    inits = {inits_tail}")
        print(f"    map nonNegSum = {mapped_tail}")
        print(f"    nonNegMaximum = {max_tail}")

    left = nonNegMaximum(lhs_mapped)
    print(f"  final LHS = nonNegMaximum({lhs_mapped}) = {left}")

    # RHS calculation
    print("RHS calculation:")
    rhs_mapped = [nonNegSum(tail) for tail in tails_xs]
    right = nonNegMaximum(rhs_mapped)
    print(f"  map nonNegSum = {rhs_mapped}")
    print(f"  final RHS = nonNegMaximum({rhs_mapped}) = {right}")

    print(f"Equal: {left == right}")
    print()

    return left == right

def test_cases():
    """Test various cases"""
    test_lists = [
        [],
        [1],
        [1, 2],
        [1, -1],
        [-1, 1],
        [1, 2, 3],
        [1, -2, 3],
    ]

    print("Testing generalised_horners_rule':")
    print("nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec = nonNegMaximum ∘ map nonNegSum ∘ tails_rec")
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
        print("All tests passed! The lemma appears to be TRUE.")
    else:
        print("Some tests failed! The lemma appears to be FALSE.")