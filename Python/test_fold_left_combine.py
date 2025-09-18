#!/usr/bin/env python3
"""
Test the fold_left_combine lemma computationally to understand what it should prove.

The lemma states that for a magma with associativity on generator elements:
m_op (fold_left m_op l1 x) (fold_left m_op l2 g) = fold_left m_op (l1 ++ g :: l2) x

where:
- l1, l2 are lists of generator elements
- g is a generator element
- x is the starting element
- m_op has middle associativity on generators
"""

def test_fold_left_combine():
    """Test the lemma with different operations and lists"""

    # Test with integer addition (commutative and associative)
    def add(a, b):
        return a + b

    def fold_left(f, lst, init):
        """Python fold_left equivalent"""
        result = init
        for item in lst:
            result = f(result, item)
        return result

    test_cases = [
        # (l1, l2, x, g)
        ([1, 2], [3, 4], 0, 5),
        ([2], [6], 1, 3),
        ([], [1, 2], 0, 5),
        ([1, 2], [], 0, 5),
        ([1], [2], 10, 3),
    ]

    print("Testing fold_left_combine lemma with addition:")
    print("=" * 60)

    for l1, l2, x, g in test_cases:
        print(f"\nTest case: l1={l1}, l2={l2}, x={x}, g={g}")

        # LHS: m_op (fold_left m_op l1 x) (fold_left m_op l2 g)
        left_fold = fold_left(add, l1, x)
        right_fold = fold_left(add, l2, g)
        lhs = add(left_fold, right_fold)

        # RHS: fold_left m_op (l1 ++ g :: l2) x
        combined_list = l1 + [g] + l2
        rhs = fold_left(add, combined_list, x)

        print(f"  LHS: add(fold_left(add, {l1}, {x}), fold_left(add, {l2}, {g}))")
        print(f"       = add({left_fold}, {right_fold}) = {lhs}")
        print(f"  RHS: fold_left(add, {combined_list}, {x}) = {rhs}")
        print(f"  Equal: {lhs == rhs}")

        if lhs != rhs:
            print("  ❌ FAILED!")
            return False
        else:
            print("  ✅ PASSED")

    print(f"\n✅ All tests passed with addition")

    # Test with multiplication (associative but not commutative)
    def mult(a, b):
        return a * b

    print(f"\n\nTesting with multiplication:")
    print("=" * 60)

    test_cases_mult = [
        ([2, 3], [4, 5], 1, 6),
        ([2], [3], 1, 4),
        ([], [2, 3], 1, 4),
        ([2, 3], [], 1, 4),
    ]

    for l1, l2, x, g in test_cases_mult:
        print(f"\nTest case: l1={l1}, l2={l2}, x={x}, g={g}")

        # LHS: m_op (fold_left m_op l1 x) (fold_left m_op l2 g)
        left_fold = fold_left(mult, l1, x)
        right_fold = fold_left(mult, l2, g)
        lhs = mult(left_fold, right_fold)

        # RHS: fold_left m_op (l1 ++ g :: l2) x
        combined_list = l1 + [g] + l2
        rhs = fold_left(mult, combined_list, x)

        print(f"  LHS: mult(fold_left(mult, {l1}, {x}), fold_left(mult, {l2}, {g}))")
        print(f"       = mult({left_fold}, {right_fold}) = {lhs}")
        print(f"  RHS: fold_left(mult, {combined_list}, {x}) = {rhs}")
        print(f"  Equal: {lhs == rhs}")

        if lhs != rhs:
            print("  ❌ FAILED!")
            return False
        else:
            print("  ✅ PASSED")

    print(f"\n✅ All tests passed with multiplication")
    return True

if __name__ == "__main__":
    success = test_fold_left_combine()
    if success:
        print(f"\n{'='*60}")
        print("✅ ALL TESTS PASSED - The lemma appears to be TRUE")
        print("The fold_left_combine lemma should be provable")
    else:
        print(f"\n{'='*60}")
        print("❌ SOME TESTS FAILED - Check lemma statement or conditions")