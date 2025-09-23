#!/usr/bin/env python3

def fold_right(f, init, lst):
    """fold_right f init [a,b,c] = f a (f b (f c init))"""
    result = init
    for x in reversed(lst):
        result = f(x, result)
    return result

def inits(lst):
    """inits [1,2,3] = [[], [1], [1,2], [1,2,3]]"""
    result = []
    for i in range(len(lst) + 1):
        result.append(lst[:i])
    return result

def compose(f, g):
    """Function composition: (f ∘ g)(x) = f(g(x))"""
    return lambda x: f(g(x))

def test_horners_rule(coeffs):
    """Test Horner's rule: fold_right (λx y → x*y + 1) 1 = fold_right (+) 0 ∘ map (fold_right (*) 1) ∘ inits"""
    # Left side: fold_right (λx y → x*y + 1) 1
    left = fold_right(lambda x, y: x * y + 1, 1, coeffs)

    # Right side: fold_right (+) 0 ∘ map (fold_right (*) 1) ∘ inits
    inits_result = inits(coeffs)
    mapped = [fold_right(lambda x, y: x * y, 1, init) for init in inits_result]
    right = fold_right(lambda x, y: x + y, 0, mapped)

    print(f"Coefficients: {coeffs}")
    print(f"Inits: {inits_result}")
    print(f"Mapped (products): {mapped}")
    print(f"Left side: {left}")
    print(f"Right side: {right}")
    print(f"Equal: {left == right}")
    print()

    return left == right

# Test with various inputs
test_cases = [
    [],
    [1],
    [1, 2],
    [1, 2, 3],
    [2, 3, 4],
    [1, 0, 1],
    [0],
    [0, 0],
    [-1, 2, -3]
]

print("Testing Horner's rule:")
print("fold_right (λx y → x*y + 1) 1 = fold_right (+) 0 ∘ map (fold_right (*) 1) ∘ inits")
print()

all_passed = True
for test_case in test_cases:
    if not test_horners_rule(test_case):
        all_passed = False

print(f"All tests passed: {all_passed}")