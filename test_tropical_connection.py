#!/usr/bin/env python3

def nonNegPlus(x, y):
    return max(0, x + y)

def fold_right_nonNegPlus(xs):
    result = 0
    for x in reversed(xs):
        result = nonNegPlus(x, result)
    return result

def fold_right_add(xs):
    return sum(xs)

def fold_right_max(xs):
    return max(xs) if xs else 0

def inits(xs):
    return [xs[:i] for i in range(len(xs) + 1)]

def test_tropical_relationship(xs):
    """Test if fold_right nonNegPlus xs = fold_right max 0 (map (fold_right add 0) (inits xs))"""

    left_side = fold_right_nonNegPlus(xs)

    # Right side: fold_right max 0 (map (fold_right add 0) (inits xs))
    prefix_sums = [fold_right_add(prefix) for prefix in inits(xs)]
    right_side = fold_right_max([0] + prefix_sums)

    print(f"xs = {xs}")
    print(f"inits(xs) = {inits(xs)}")
    print(f"prefix_sums = {prefix_sums}")
    print(f"left_side (nonNegSum) = {left_side}")
    print(f"right_side (max of prefix sums) = {right_side}")
    print(f"Equal: {left_side == right_side}")
    print()

    return left_side == right_side

# Test with various lists
test_cases = [
    [],
    [1],
    [1, 2],
    [1, -2],
    [-1, 2],
    [-1, -2],
    [1, 2, 3],
    [1, -3, 2],
    [-1, 3, -2],
    [3, -5, 4, -2, 1]
]

print("Testing tropical relationship:")
print("fold_right nonNegPlus xs =?= fold_right max 0 (map (fold_right add 0) (inits xs))")
print("=" * 80)

all_passed = True
for xs in test_cases:
    passed = test_tropical_relationship(xs)
    if not passed:
        all_passed = False

print("=" * 80)
print(f"All tests passed: {all_passed}")