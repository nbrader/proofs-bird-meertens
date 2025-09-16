#!/usr/bin/env python3
"""
CORRECTED test script for generalised_horners_rule lemma.

Testing: fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits

Where:
- x <#> y = nonNegPlus x y = max(0, x + y)
- x <|> y = Z.max x y = max(x, y)
- The operation (x <#> y <|> 0) = max(nonNegPlus(x, y), 0) = max(max(0, x + y), 0) = max(0, x + y)
  So actually (x <#> y <|> 0) = nonNegPlus(x, y)

But wait, let me double-check the Coq definitions...
"""

def nonNegPlus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def z_max(x, y):
    """Z.max operation"""
    return max(x, y)

def tropical_horner_op(x, y):
    """The operation: x <#> y <|> 0
    This is: max(nonNegPlus(x, y), 0)
    Since nonNegPlus(x, y) = max(0, x + y), this becomes:
    max(max(0, x + y), 0) = max(0, x + y) = nonNegPlus(x, y)
    """
    return max(nonNegPlus(x, y), 0)

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

def debug_case(xs):
    """Debug a specific case in detail"""
    print(f"Debugging case: {xs}")

    # LHS calculation
    print("LHS: fold_right tropical_horner_op 0")
    def debug_fold_right(op, init, xs, depth=0):
        indent = "  " * depth
        if not xs:
            print(f"{indent}base case: {init}")
            return init
        print(f"{indent}op({xs[0]}, fold_right(..., {xs[1:]}))")
        rest = debug_fold_right(op, init, xs[1:], depth+1)
        result = op(xs[0], rest)
        print(f"{indent}= op({xs[0]}, {rest}) = {result}")
        return result

    left = debug_fold_right(tropical_horner_op, 0, xs)
    print(f"LHS result: {left}")
    print()

    # RHS calculation
    print("RHS: nonNegMaximum ∘ map nonNegSum ∘ inits")
    inits_xs = inits(xs)
    print(f"inits({xs}) = {inits_xs}")
    mapped = [nonNegSum(seg) for seg in inits_xs]
    print(f"map nonNegSum = {mapped}")
    right = nonNegMaximum(mapped)
    print(f"nonNegMaximum = {right}")
    print(f"RHS result: {right}")
    print()

    print(f"Equal? {left == right}")
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
    ]

    print("Testing generalised_horners_rule (CORRECTED):")
    print("fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits")
    print()

    # First test if tropical_horner_op is equivalent to nonNegPlus
    print("Testing if tropical_horner_op(x, y) == nonNegPlus(x, y):")
    test_pairs = [(1, 2), (1, -1), (-1, 1), (-1, -2), (0, 0)]
    for x, y in test_pairs:
        th_result = tropical_horner_op(x, y)
        nnp_result = nonNegPlus(x, y)
        print(f"  tropical_horner_op({x}, {y}) = {th_result}, nonNegPlus({x}, {y}) = {nnp_result}, equal: {th_result == nnp_result}")
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
            print("  Debugging this case:")
            debug_case(xs)
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