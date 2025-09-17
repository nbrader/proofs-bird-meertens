#!/usr/bin/env python3
"""
Deep analysis of the inductive structure for fold_right_nonNegPlus_eq_max_prefixes:
nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))

This will help understand what mathematical properties are needed for the proof.
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

def debug_inductive_step(x, xs_rest):
    """
    Analyze the inductive step: given x :: xs_rest,
    what's the relationship between:
    - LHS: nonNegSum(x :: xs_rest)
    - RHS: nonNegMaximum(map nonNegSum (inits (x :: xs_rest)))
    """

    full_list = [x] + xs_rest

    print(f"Analyzing: {x} :: {xs_rest} = {full_list}")

    # LHS: nonNegSum(x :: xs_rest)
    lhs = nonNegSum(full_list)
    rest_sum = nonNegSum(xs_rest)
    print(f"LHS: nonNegSum({full_list}) = {x} <#> nonNegSum({xs_rest}) = {x} <#> {rest_sum} = {lhs}")

    # RHS: nonNegMaximum(map nonNegSum (inits (x :: xs_rest)))
    inits_full = inits(full_list)
    print(f"inits({full_list}) = {inits_full}")

    mapped = [nonNegSum(seg) for seg in inits_full]
    print("map nonNegSum:")
    for i, (seg, sum_val) in enumerate(zip(inits_full, mapped)):
        print(f"  {seg} -> {sum_val}")

    rhs = nonNegMaximum(mapped)
    print(f"RHS: nonNegMaximum({mapped}) = {rhs}")

    # Key insight: inits(x :: xs_rest) = [[]] + [[x]] + map (cons x) (inits xs_rest)
    # So the mapped values are: [0] + [x] + map (x <#> ·) (map nonNegSum (inits xs_rest))

    # Induction hypothesis would give us:
    # nonNegSum(xs_rest) = nonNegMaximum(map nonNegSum (inits xs_rest))

    # So we need to show that:
    # x <#> nonNegSum(xs_rest) = max(0, x, max over (x <#> prefix_sums))

    print(f"\nInduction hypothesis: nonNegSum({xs_rest}) should equal max of prefix sums of {xs_rest}")
    inits_rest = inits(xs_rest)
    prefix_sums_rest = [nonNegSum(seg) for seg in inits_rest]
    max_prefix_sums_rest = nonNegMaximum(prefix_sums_rest)
    print(f"  inits({xs_rest}) = {inits_rest}")
    print(f"  prefix sums = {prefix_sums_rest}")
    print(f"  max = {max_prefix_sums_rest}")
    print(f"  IH check: {rest_sum} == {max_prefix_sums_rest} ? {rest_sum == max_prefix_sums_rest}")

    # Now analyze the structure
    print(f"\nKey relationship:")
    print(f"  First element of RHS: nonNegSum([]) = 0")
    print(f"  Second element of RHS: nonNegSum([{x}]) = {x}")
    print(f"  Remaining elements: map (nonNegPlus {x}) {prefix_sums_rest} = {[nonNegPlus(x, s) for s in prefix_sums_rest]}")

    # The maximum should be max(0, x, max(map (nonNegPlus x) prefix_sums_rest))
    candidate_max = z_max(z_max(0, x), nonNegMaximum([nonNegPlus(x, s) for s in prefix_sums_rest]))
    print(f"  Predicted RHS: max(0, {x}, max({[nonNegPlus(x, s) for s in prefix_sums_rest]})) = {candidate_max}")

    print(f"\nFinal check: LHS = {lhs}, RHS = {rhs}, Equal = {lhs == rhs}")
    print()

    return lhs == rhs

def test_inductive_cases():
    """Test various inductive cases"""
    test_cases = [
        (1, []),
        (1, [2]),
        (1, [-1]),
        (1, [2, 3]),
        (-1, [2]),
        (-2, [1, 2]),
        (3, [1, -2, 3]),
        (0, [1, -1]),
    ]

    print("Testing inductive structure of fold_right_nonNegPlus_eq_max_prefixes:")
    print("nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))")
    print()

    passed = 0
    failed = 0

    for x, xs_rest in test_cases:
        if debug_inductive_step(x, xs_rest):
            passed += 1
        else:
            failed += 1

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_inductive_cases()
    if success:
        print("All inductive cases work! Ready to develop proof strategy.")
    else:
        print("Some cases failed - need to understand the pattern better.")