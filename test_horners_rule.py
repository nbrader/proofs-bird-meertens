#!/usr/bin/env python3
"""
Test script for generalised_horners_rule lemma.

Testing: fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits

Where:
- x <#> y = nonNegPlus x y = max(0, x + y)
- x <|> y = Z.max x y
- nonNegSum xs = fold_right nonNegPlus 0 xs
- nonNegMaximum = fold_right Z.max 0
- inits returns all initial segments of a list
"""

def nonNegPlus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def z_max(x, y):
    """Z.max operation"""
    return max(x, y)

def tropical_horner_op(x, y):
    """The operation: x <#> y <|> 0 = max(0, nonNegPlus(x, y))"""
    return z_max(nonNegPlus(x, y), 0)

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

def lhs(xs):
    """Left side: fold_right (fun x y : Z => x <#> y <|> 0) 0"""
    return fold_right(tropical_horner_op, 0, xs)

def rhs(xs):
    """Right side: nonNegMaximum ∘ map nonNegSum ∘ inits"""
    inits_xs = inits(xs)
    mapped = [nonNegSum(seg) for seg in inits_xs]
    return nonNegMaximum(mapped)

def test_equality(xs):
    """Test if lhs(xs) == rhs(xs)"""
    left = lhs(xs)
    right = rhs(xs)
    return left == right, left, right

def test_cases():
    """Test various cases"""
    test_lists = [
        [],
        [0],
        [1],
        [-1],
        [1, 2],
        [1, -1],
        [-1, 1],
        [-1, -1],
        [1, 2, 3],
        [1, -2, 3],
        [-1, -2, -3],
        [5, -3, 2, -1],
        [0, 0, 0],
        [1, 0, -1, 2],
        [-5, 10, -3, 7, -2]
    ]

    print("Testing generalised_horners_rule:")
    print("fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits")
    print()

    passed = 0
    failed = 0

    for xs in test_lists:
        equal, left, right = test_equality(xs)
        if equal:
            print(f"✓ {xs}: {left} = {right}")
            passed += 1
        else:
            print(f"✗ {xs}: {left} ≠ {right}")
            # Show detailed breakdown
            inits_xs = inits(xs)
            mapped = [nonNegSum(seg) for seg in inits_xs]
            print(f"  inits({xs}) = {inits_xs}")
            print(f"  map nonNegSum = {mapped}")
            print(f"  nonNegMaximum = {right}")
            print(f"  fold_right tropical_horner_op = {left}")
            failed += 1
        print()

    print(f"Results: {passed} passed, {failed} failed")
    return failed == 0

if __name__ == "__main__":
    success = test_cases()
    if success:
        print("All tests passed! The lemma appears to be TRUE.")
    else:
        print("Some tests failed! The lemma appears to be FALSE.")