#!/usr/bin/env python3
"""
Test the specific subgoal in fold_left_combine proof:
m_op (fold_left m_op l1 x) (fold_left m_op l2 g) =
fold_left m_op l2 (m_op (fold_left m_op l1 x) g)

This tests whether the middle associativity property holds for fold_left operations.
"""

def fold_left(op, lst, init):
    """Fold left operation: fold_left(op, [a,b,c], init) = op(op(op(init, a), b), c)"""
    result = init
    for x in lst:
        result = op(result, x)
    return result

def test_fold_left_middle_associativity(op, l1, l2, x, g):
    """
    Test: op(fold_left(op, l1, x), fold_left(op, l2, g)) =
          fold_left(op, l2, op(fold_left(op, l1, x), g))
    """
    # Left side: op(fold_left(op, l1, x), fold_left(op, l2, g))
    left_fold_l1 = fold_left(op, l1, x)
    left_fold_l2 = fold_left(op, l2, g)
    lhs = op(left_fold_l1, left_fold_l2)

    # Right side: fold_left(op, l2, op(fold_left(op, l1, x), g))
    right_init = op(left_fold_l1, g)
    rhs = fold_left(op, l2, right_init)

    return lhs == rhs

def test_with_addition():
    """Test with addition (commutative and associative)"""
    print("Testing with addition (+):")

    test_cases = [
        ([1, 2], [3, 4], 0, 5),
        ([2], [1, 3], 1, 4),
        ([], [1, 2, 3], 5, 2),
        ([1, 2, 3], [], 0, 7),
        ([1], [2], 3, 4),
        ([5, 6, 7], [8, 9], 10, 11),
    ]

    all_passed = True
    for i, (l1, l2, x, g) in enumerate(test_cases):
        result = test_fold_left_middle_associativity(lambda a, b: a + b, l1, l2, x, g)
        print(f"  Test {i+1}: l1={l1}, l2={l2}, x={x}, g={g} -> {'PASS' if result else 'FAIL'}")
        if not result:
            all_passed = False
            # Show the actual values for debugging
            left_fold_l1 = fold_left(lambda a, b: a + b, l1, x)
            left_fold_l2 = fold_left(lambda a, b: a + b, l2, g)
            lhs = left_fold_l1 + left_fold_l2
            right_init = left_fold_l1 + g
            rhs = fold_left(lambda a, b: a + b, l2, right_init)
            print(f"    LHS: {left_fold_l1} + {left_fold_l2} = {lhs}")
            print(f"    RHS: fold_left(+, {l2}, {right_init}) = {rhs}")

    print(f"Addition tests: {'ALL PASSED' if all_passed else 'SOME FAILED'}")
    return all_passed

def test_with_multiplication():
    """Test with multiplication (commutative and associative)"""
    print("\nTesting with multiplication (*):")

    test_cases = [
        ([2, 3], [4, 5], 1, 6),
        ([2], [3, 4], 1, 5),
        ([], [2, 3, 4], 5, 6),
        ([2, 3, 4], [], 1, 7),
        ([2], [3], 4, 5),
        ([2, 3], [4, 5], 6, 7),
    ]

    all_passed = True
    for i, (l1, l2, x, g) in enumerate(test_cases):
        result = test_fold_left_middle_associativity(lambda a, b: a * b, l1, l2, x, g)
        print(f"  Test {i+1}: l1={l1}, l2={l2}, x={x}, g={g} -> {'PASS' if result else 'FAIL'}")
        if not result:
            all_passed = False
            # Show the actual values for debugging
            left_fold_l1 = fold_left(lambda a, b: a * b, l1, x)
            left_fold_l2 = fold_left(lambda a, b: a * b, l2, g)
            lhs = left_fold_l1 * left_fold_l2
            right_init = left_fold_l1 * g
            rhs = fold_left(lambda a, b: a * b, l2, right_init)
            print(f"    LHS: {left_fold_l1} * {left_fold_l2} = {lhs}")
            print(f"    RHS: fold_left(*, {l2}, {right_init}) = {rhs}")

    print(f"Multiplication tests: {'ALL PASSED' if all_passed else 'SOME FAILED'}")
    return all_passed

def test_with_max():
    """Test with max operation (commutative and associative)"""
    print("\nTesting with max operation:")

    test_cases = [
        ([1, 3], [2, 4], 0, 5),
        ([7], [1, 9], 2, 6),
        ([], [1, 2, 3], 5, 4),
        ([8, 2, 6], [], 1, 9),
        ([3], [7], 2, 5),
        ([1, 4], [2, 8], 3, 6),
    ]

    all_passed = True
    for i, (l1, l2, x, g) in enumerate(test_cases):
        result = test_fold_left_middle_associativity(max, l1, l2, x, g)
        print(f"  Test {i+1}: l1={l1}, l2={l2}, x={x}, g={g} -> {'PASS' if result else 'FAIL'}")
        if not result:
            all_passed = False
            # Show the actual values for debugging
            left_fold_l1 = fold_left(max, l1, x)
            left_fold_l2 = fold_left(max, l2, g)
            lhs = max(left_fold_l1, left_fold_l2)
            right_init = max(left_fold_l1, g)
            rhs = fold_left(max, l2, right_init)
            print(f"    LHS: max({left_fold_l1}, {left_fold_l2}) = {lhs}")
            print(f"    RHS: fold_left(max, {l2}, {right_init}) = {rhs}")

    print(f"Max tests: {'ALL PASSED' if all_passed else 'SOME FAILED'}")
    return all_passed

def test_non_commutative_operation():
    """Test with subtraction (non-commutative, non-associative)"""
    print("\nTesting with subtraction (non-commutative, non-associative):")

    test_cases = [
        ([1, 2], [3, 4], 10, 5),
        ([2], [1, 3], 10, 4),
        ([], [1, 2, 3], 10, 2),
        ([1, 2, 3], [], 10, 7),
        ([1], [2], 10, 4),
    ]

    all_passed = True
    for i, (l1, l2, x, g) in enumerate(test_cases):
        result = test_fold_left_middle_associativity(lambda a, b: a - b, l1, l2, x, g)
        print(f"  Test {i+1}: l1={l1}, l2={l2}, x={x}, g={g} -> {'PASS' if result else 'FAIL'}")
        if not result:
            all_passed = False
            # Show the actual values for debugging
            left_fold_l1 = fold_left(lambda a, b: a - b, l1, x)
            left_fold_l2 = fold_left(lambda a, b: a - b, l2, g)
            lhs = left_fold_l1 - left_fold_l2
            right_init = left_fold_l1 - g
            rhs = fold_left(lambda a, b: a - b, l2, right_init)
            print(f"    LHS: {left_fold_l1} - {left_fold_l2} = {lhs}")
            print(f"    RHS: fold_left(-, {l2}, {right_init}) = {rhs}")

    print(f"Subtraction tests: {'ALL PASSED' if all_passed else 'SOME FAILED'}")
    return all_passed

if __name__ == "__main__":
    print("Testing fold_left middle associativity subgoal:")
    print("Goal: op(fold_left(op, l1, x), fold_left(op, l2, g)) = fold_left(op, l2, op(fold_left(op, l1, x), g))")
    print("=" * 80)

    # Test with various operations
    add_passed = test_with_addition()
    mult_passed = test_with_multiplication()
    max_passed = test_with_max()
    sub_passed = test_non_commutative_operation()

    print("\n" + "=" * 80)
    print("SUMMARY:")
    print(f"Addition (commutative, associative): {'PASS' if add_passed else 'FAIL'}")
    print(f"Multiplication (commutative, associative): {'PASS' if mult_passed else 'FAIL'}")
    print(f"Max (commutative, associative): {'PASS' if max_passed else 'FAIL'}")
    print(f"Subtraction (non-commutative, non-associative): {'PASS' if sub_passed else 'FAIL'}")

    if add_passed and mult_passed and max_passed:
        print("\n✅ The subgoal appears to be TRUE for associative and commutative operations!")
        print("   This suggests the proof approach is mathematically sound.")
    elif not sub_passed:
        print("\n⚠️  The subgoal fails for non-associative operations (as expected).")
        print("   This suggests we need to use the associativity property in the proof.")
    else:
        print("\n❌ Unexpected results - need to investigate further.")