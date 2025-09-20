#!/usr/bin/env python3

def test_max_distrib():
    """Test that max(max(a, b), c) = max(max(a, c), max(b, c))"""

    test_cases = [
        (1, 2, 3),
        (3, 2, 1),
        (2, 1, 3),
        (1, 3, 2),
        (2, 3, 1),
        (3, 1, 2),
        (0, 0, 0),
        (1, 1, 1),
        (-1, -2, -3),
        (-3, -1, -2),
        (5, -10, 15),
        (-5, 10, -15),
        (0, 5, -5),
        (100, 200, 150),
    ]

    for a, b, c in test_cases:
        left = max(max(a, b), c)
        right = max(max(a, c), max(b, c))
        print(f"max(max({a}, {b}), {c}) = {left}")
        print(f"max(max({a}, {c}), max({b}, {c})) = {right}")
        print(f"Equal: {left == right}")

        if left != right:
            print(f"FAILURE: {a}, {b}, {c}")
            return False
        print()

    return True

if __name__ == "__main__":
    print("Testing max distribution property...")
    success = test_max_distrib()
    print(f"All tests passed: {success}")