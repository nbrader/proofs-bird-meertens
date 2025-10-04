#!/usr/bin/env python3

def nonneg_plus(x, y):
    """Non-negative addition: if x + y >= 0 then x + y else 0"""
    result = x + y
    return result if result >= 0 else 0

def nonneg_sum(xs):
    """fold_right nonNegPlus 0 xs"""
    result = 0
    for x in reversed(xs):
        result = nonneg_plus(x, result)
    return result

def regular_sum(xs):
    """fold_right Z.add 0 xs"""
    return sum(xs)

def test_lemma():
    """Test if: when regular_sum(xs) >= 0, then nonneg_sum(xs) >= regular_sum(xs)"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [2, -1],
        [3, -1],
        [1, -2, 3],
        [5, -2, -1],
        [1, 1, 1],
        [0, 0, 0],
        [-1, 2, -3, 4],  # sum = 2
        [10, -5, -3, 1],  # sum = 3
    ]

    print("Testing lemma: when regular_sum(xs) >= 0, then nonneg_sum(xs) >= regular_sum(xs)")
    print()

    for xs in test_cases:
        reg_sum = regular_sum(xs)
        if reg_sum >= 0:  # Only test when condition holds
            nn_sum = nonneg_sum(xs)
            holds = nn_sum >= reg_sum
            print(f"xs = {xs}")
            print(f"  regular_sum = {reg_sum}")
            print(f"  nonneg_sum = {nn_sum}")
            print(f"  nonneg_sum >= regular_sum: {holds}")
            print()

            if not holds:
                print("COUNTEREXAMPLE FOUND!")
                return False

    print("All tests passed!")
    return True

if __name__ == "__main__":
    test_lemma()