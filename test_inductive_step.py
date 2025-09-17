#!/usr/bin/env python3
"""
Test the specific inductive step property:
For x :: xs', we need to show:
x <#> fold_right nonNegPlus 0 xs' = fold_right Z.max 0 (map (fun l => x <#> fold_right nonNegPlus 0 l) (inits xs'))

This is testing whether nonNegPlus distributes properly over the fold_right Z.max operation.
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

def inits(xs):
    """Return all initial segments of xs, including empty list"""
    result = [[]]
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def test_inductive_property(x, xs_prime):
    """Test the inductive step property"""
    # LHS: x <#> fold_right nonNegPlus 0 xs'
    sum_xs_prime = fold_right(nonNegPlus, 0, xs_prime)
    lhs = nonNegPlus(x, sum_xs_prime)

    # RHS: fold_right Z.max 0 (map (fun l => x <#> fold_right nonNegPlus 0 l) (inits xs'))
    inits_xs_prime = inits(xs_prime)
    mapped = []
    for init_seg in inits_xs_prime:
        seg_sum = fold_right(nonNegPlus, 0, init_seg)
        x_plus_seg = nonNegPlus(x, seg_sum)
        mapped.append(x_plus_seg)
    rhs = fold_right(z_max, 0, mapped)

    print(f"x = {x}, xs' = {xs_prime}")
    print(f"sum(xs') = {sum_xs_prime}")
    print(f"LHS: x <#> sum(xs') = {x} <#> {sum_xs_prime} = {lhs}")
    print(f"inits(xs') = {inits_xs_prime}")

    for i, (init_seg, mapped_val) in enumerate(zip(inits_xs_prime, mapped)):
        seg_sum = fold_right(nonNegPlus, 0, init_seg)
        print(f"  {init_seg} -> sum={seg_sum}, x <#> sum = {x} <#> {seg_sum} = {mapped_val}")

    print(f"RHS: max({mapped}) = {rhs}")
    print(f"Equal: {lhs == rhs}")
    print()

    return lhs == rhs

def test_cases():
    """Test various cases for the inductive property"""
    test_pairs = [
        (1, []),
        (1, [2]),
        (1, [-1]),
        (1, [2, 3]),
        (1, [-2, 3]),
        (-1, [2]),
        (-1, [-1]),
        (3, [1, -2, 3]),
        (-2, [1, 2]),
    ]

    print("Testing inductive step property:")
    print("x <#> fold_right nonNegPlus 0 xs' = fold_right Z.max 0 (map (x <#> fold_right nonNegPlus 0) (inits xs'))")
    print()

    passed = 0
    failed = 0

    for x, xs_prime in test_pairs:
        if test_inductive_property(x, xs_prime):
            passed += 1
        else:
            failed += 1

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("All tests passed! The inductive property holds.")
    else:
        print("Some tests failed! The inductive property does not hold.")