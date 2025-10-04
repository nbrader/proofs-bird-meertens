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

def inits(xs):
    """All initial segments of a list"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def test_h_rhs_eq_base_case():
    """Test base case: xs = []"""
    print("Testing H_rhs_eq base case (xs = []):")

    xs = []

    # LHS (simplified): should be 0 for empty case
    lhs_result = 0  # This is what the tropical operations should give for empty list

    # RHS: fold_right Z.max 0 (map (fold_right Z.add 0) (inits xs))
    inits_xs = inits(xs)  # [[]]
    print(f"  inits(xs) = {inits_xs}")

    mapped_sums = [regular_sum(prefix) for prefix in inits_xs]  # [0]
    print(f"  map regular_sum inits(xs) = {mapped_sums}")

    rhs_result = max([0] + mapped_sums)  # max(0, 0) = 0
    print(f"  fold_right Z.max 0 mapped_sums = {rhs_result}")

    print(f"  LHS = {lhs_result}")
    print(f"  RHS = {rhs_result}")
    print(f"  Equal: {lhs_result == rhs_result}")
    print()

    return lhs_result == rhs_result

def test_h_rhs_eq_simple_cases():
    """Test simple cases to see if the correspondence holds"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [2, -1],
        [-1, 3],
        [1, -2, 3],
        [0, 0, 0],
    ]

    print("Testing H_rhs_eq correspondence for simple cases:")
    print("Note: This is a simplified test since we don't have the full tropical operations")
    print()

    for xs in test_cases:
        print(f"xs = {xs}")

        # What we're trying to prove:
        # fold_right StructSemiring.add_op StructSemiring.add_zero
        #   (map (fold_right StructSemiring.mul_op StructSemiring.mul_one) (inits (map Finite xs)))
        # = Finite (fold_right Z.max 0 (map (fold_right Z.add 0) (inits xs)))

        # RHS: fold_right Z.max 0 (map (fold_right Z.add 0) (inits xs))
        inits_xs = inits(xs)
        print(f"  inits(xs) = {inits_xs}")

        mapped_sums = [regular_sum(prefix) for prefix in inits_xs]
        print(f"  map regular_sum inits(xs) = {mapped_sums}")

        rhs_result = max([0] + mapped_sums) if mapped_sums else 0
        print(f"  fold_right Z.max 0 mapped_sums = {rhs_result}")

        # For comparison, let's see what nonNegSum gives us
        nonneg_result = nonneg_sum(xs)
        print(f"  nonNegSum(xs) = {nonneg_result}")

        print(f"  RHS result = {rhs_result}")
        print(f"  NonNegSum = {nonneg_result}")
        print()

def test_inits_map_relationship():
    """Test the relationship between inits(map(...)) and map(..., inits(...))"""
    print("Testing inits/map relationship:")
    print("Does inits(map(f, xs)) = map(map(f), inits(xs))?")
    print()

    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
    ]

    def f(x):
        return x + 10  # Simple function for testing

    for xs in test_cases:
        print(f"xs = {xs}")

        # LHS: inits(map(f, xs))
        mapped_xs = [f(x) for x in xs]
        lhs = inits(mapped_xs)
        print(f"  inits(map(f, xs)) = inits({mapped_xs}) = {lhs}")

        # RHS: map(map(f), inits(xs))
        inits_xs = inits(xs)
        rhs = [[f(x) for x in prefix] for prefix in inits_xs]
        print(f"  map(map(f), inits(xs)) = map(map(f), {inits_xs}) = {rhs}")

        equal = lhs == rhs
        print(f"  Equal: {equal}")
        print()

        if not equal:
            print("  COUNTEREXAMPLE FOUND!")
            return False

    print("All tests passed!")
    return True

if __name__ == "__main__":
    print("=== Verifying H_rhs_eq subgoals ===")
    print()

    test_h_rhs_eq_base_case()
    test_h_rhs_eq_simple_cases()
    test_inits_map_relationship()