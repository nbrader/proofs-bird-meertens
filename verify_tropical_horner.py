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

def nonneg_maximum(xs):
    """fold_right max 0 xs"""
    result = 0
    for x in reversed(xs):
        result = max(x, result)
    return result

def inits(xs):
    """All initial segments of xs"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def tropical_horner_op(x, y):
    """Tropical Horner operation: (x <#> y) <|> 1"""
    return max(nonneg_plus(x, y), 1)

def tropical_horner(xs):
    """fold_right tropical_horner_op 1 xs"""
    result = 1
    for x in reversed(xs):
        result = tropical_horner_op(x, result)
    return result

def test_tropical_horner_rule():
    """Test if tropical_horner = nonneg_maximum ∘ map nonneg_sum ∘ inits"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [-1, 2, -3, 4],
        [0, 0, 0],
        [-5, -4, -3],
        [5, -10, 3, -2, 1]
    ]

    print("Testing tropical Horner rule:")
    print("tropical_horner(xs) =?= nonneg_maximum(map(nonneg_sum, inits(xs)))")
    print()

    for xs in test_cases:
        left = tropical_horner(xs)

        inits_xs = inits(xs)
        mapped = [nonneg_sum(prefix) for prefix in inits_xs]
        right = nonneg_maximum(mapped)

        match = left == right
        print(f"xs = {xs}")
        print(f"  tropical_horner: {left}")
        print(f"  inits: {inits_xs}")
        print(f"  mapped sums: {mapped}")
        print(f"  max of mapped: {right}")
        print(f"  Match: {match}")
        print()

        if not match:
            print("MISMATCH FOUND!")
            return False

    print("All tests passed!")
    return True

def test_original_claim():
    """Test the original claim: nonneg_sum = nonneg_maximum ∘ map nonneg_sum ∘ inits"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [-1, 2, -3, 4],
        [0, 0, 0],
        [-5, -4, -3],
        [5, -10, 3, -2, 1]
    ]

    print("Testing original claim:")
    print("nonneg_sum(xs) =?= nonneg_maximum(map(nonneg_sum, inits(xs)))")
    print()

    for xs in test_cases:
        left = nonneg_sum(xs)

        inits_xs = inits(xs)
        mapped = [nonneg_sum(prefix) for prefix in inits_xs]
        right = nonneg_maximum(mapped)

        match = left == right
        print(f"xs = {xs}")
        print(f"  nonneg_sum: {left}")
        print(f"  inits: {inits_xs}")
        print(f"  mapped sums: {mapped}")
        print(f"  max of mapped: {right}")
        print(f"  Match: {match}")
        print()

        if not match:
            print("MISMATCH FOUND!")
            return False

    print("All tests passed!")
    return True

if __name__ == "__main__":
    print("=== Testing Original Claim ===")
    test_original_claim()
    print("\n=== Testing Tropical Horner Rule ===")
    test_tropical_horner_rule()