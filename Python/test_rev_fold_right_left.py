#!/usr/bin/env python3

"""
Test the rev_fold_right_left proposition:
fold_left (fun x acc => cons acc x) l [] = rev (fold_right cons [] l)

This tests whether the proposition is mathematically correct before attempting the Coq proof.
"""

def fold_left(f, lst, init):
    """fold_left f lst init applies f from left to right"""
    acc = init
    for x in lst:
        acc = f(acc, x)
    return acc

def fold_right(f, lst, init):
    """fold_right f lst init applies f from right to left"""
    acc = init
    for x in reversed(lst):
        acc = f(x, acc)
    return acc

def cons(x, xs):
    """cons operation: prepend x to list xs"""
    return [x] + xs

def test_rev_fold_right_left():
    """Test the proposition on various lists"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [1, 2, 3, 4],
        ['a', 'b', 'c'],
        [10, 20, 30, 40, 50]
    ]

    print("Testing rev_fold_right_left proposition:")
    print("fold_left (fun x acc => cons acc x) l [] = rev (fold_right cons [] l)")
    print()

    all_pass = True

    for i, lst in enumerate(test_cases):
        # LHS: fold_left (fun x acc => cons acc x) l []
        # In Python: fold_left(lambda acc, x: cons(x, acc), lst, [])
        lhs = fold_left(lambda acc, x: cons(x, acc), lst, [])

        # RHS: rev (fold_right cons [] l)
        # fold_right cons [] l builds the list normally
        fold_result = fold_right(cons, lst, [])
        rhs = list(reversed(fold_result))

        passed = lhs == rhs
        all_pass = all_pass and passed

        print(f"Test {i+1}: {lst}")
        print(f"  LHS (fold_left): {lhs}")
        print(f"  fold_right cons: {fold_result}")
        print(f"  RHS (rev fold_right): {rhs}")
        print(f"  Equal: {passed}")
        print()

    print(f"Overall result: {'✅ ALL TESTS PASS' if all_pass else '❌ SOME TESTS FAIL'}")

    # Let's trace through a simple example step by step
    print("\n" + "="*50)
    print("DETAILED TRACE for [1, 2, 3]:")
    lst = [1, 2, 3]

    print("\nLHS: fold_left (fun x acc => cons acc x) [1,2,3] []")
    print("  Start: acc = []")
    print("  Step 1: x=1, acc = cons(1, []) = [1]")
    print("  Step 2: x=2, acc = cons(2, [1]) = [2, 1]")
    print("  Step 3: x=3, acc = cons(3, [2, 1]) = [3, 2, 1]")
    print("  Final: [3, 2, 1]")

    print("\nRHS: rev (fold_right cons [] [1,2,3])")
    print("  fold_right cons [] [1,2,3]:")
    print("    Start from right: acc = []")
    print("    Step 1: cons(3, []) = [3]")
    print("    Step 2: cons(2, [3]) = [2, 3]")
    print("    Step 3: cons(1, [2, 3]) = [1, 2, 3]")
    print("  fold_right result: [1, 2, 3]")
    print("  rev([1, 2, 3]) = [3, 2, 1]")
    print("  Final: [3, 2, 1]")

    return all_pass

if __name__ == "__main__":
    test_rev_fold_right_left()