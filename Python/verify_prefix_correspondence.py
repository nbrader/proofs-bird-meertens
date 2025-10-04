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

def prefix_sums_all_nonneg(xs):
    """Check if all prefix sums are non-negative"""
    cumulative = 0
    for x in xs:
        cumulative += x
        if cumulative < 0:
            return False
    return True

def test_prefix_correspondence():
    """Test: when all prefix sums are non-negative, does nonNegSum = regular_sum?"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [2, 1, 3],
        [3, 2, 1],
        [1, 1, 1, 1],
        [5, 0, 0, 2],
        [0, 0, 0],
        [1, 0, 2, 0, 3],
    ]

    print("Testing prefix correspondence:")
    print("When all prefix sums >= 0, does nonneg_sum = regular_sum?")
    print()

    for xs in test_cases:
        if prefix_sums_all_nonneg(xs):  # Only test when condition holds
            nn_sum = nonneg_sum(xs)
            reg_sum = regular_sum(xs)
            equal = nn_sum == reg_sum

            # Show prefix sums
            prefix_sums = []
            cumulative = 0
            for x in xs:
                cumulative += x
                prefix_sums.append(cumulative)

            print(f"xs = {xs}")
            print(f"  prefix sums: {prefix_sums}")
            print(f"  nonneg_sum: {nn_sum}")
            print(f"  regular_sum: {reg_sum}")
            print(f"  Equal: {equal}")
            print()

            if not equal:
                print("COUNTEREXAMPLE FOUND!")
                return False

    print("All tests passed!")
    return True

if __name__ == "__main__":
    test_prefix_correspondence()