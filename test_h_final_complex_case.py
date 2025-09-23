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

def nonneg_maximum(xs):
    """fold_right Z.max 0 xs"""
    return max([0] + xs) if xs else 0

def test_h_final_complex_case():
    """Test H_final correspondence when some prefix elements are negative"""
    test_cases = [
        [-1, 2],      # prefix has negative element
        [-2, 3, 1],   # prefix has negative element
        [1, -2, 4],   # prefix has negative element
        [-1, -1, 5],  # prefix has multiple negative elements
        [2, -5, 3],   # middle negative causes issues
    ]

    print("Testing H_final complex case (negative elements in prefix):")
    print("Does fold_right Z.max 0 (map regular_sum (inits xs)) = nonNegMaximum (map nonNegSum (inits xs))?")
    print()

    for xs in test_cases:
        print(f"xs = {xs}")

        # LHS: fold_right Z.max 0 (map regular_sum (inits xs))
        inits_xs = inits(xs)
        print(f"  inits(xs) = {inits_xs}")

        regular_sums = [regular_sum(prefix) for prefix in inits_xs]
        print(f"  map regular_sum inits(xs) = {regular_sums}")

        lhs = max([0] + regular_sums)
        print(f"  LHS = fold_right Z.max 0 = {lhs}")

        # RHS: nonNegMaximum (map nonNegSum (inits xs))
        nonneg_sums = [nonneg_sum(prefix) for prefix in inits_xs]
        print(f"  map nonNegSum inits(xs) = {nonneg_sums}")

        rhs = nonneg_maximum(nonneg_sums)
        print(f"  RHS = nonNegMaximum = {rhs}")

        equal = lhs == rhs
        print(f"  Equal: {equal}")

        if not equal:
            print(f"  MISMATCH! LHS={lhs}, RHS={rhs}")
            print(f"  Difference analysis:")
            for i, (reg, nonneg) in enumerate(zip(regular_sums, nonneg_sums)):
                if reg != nonneg:
                    print(f"    prefix {inits_xs[i]}: regular_sum={reg}, nonneg_sum={nonneg}")
        print()

def test_individual_prefix_correspondence():
    """Test when individual prefixes satisfy fold_right Z.add 0 = nonNegSum"""
    test_prefixes = [
        [],
        [-1],
        [-1, 2],
        [-2, 3],
        [1, -2],
        [-1, -1, 5],
        [2, -5],
    ]

    print("Testing individual prefix correspondence:")
    print("When does fold_right Z.add 0 prefix = nonNegSum prefix?")
    print()

    for prefix in test_prefixes:
        regular = regular_sum(prefix)
        nonneg = nonneg_sum(prefix)
        equal = regular == nonneg

        # Check prefix sum property
        prefix_sums = []
        cumulative = 0
        for x in prefix:
            cumulative += x
            prefix_sums.append(cumulative)

        all_prefix_nonneg = all(ps >= 0 for ps in prefix_sums)

        print(f"prefix = {prefix}")
        print(f"  regular_sum = {regular}")
        print(f"  nonneg_sum = {nonneg}")
        print(f"  equal = {equal}")
        print(f"  prefix_sums = {prefix_sums}")
        print(f"  all_prefix_sums_nonneg = {all_prefix_nonneg}")
        print(f"  correspondence holds when all_prefix_sums_nonneg = {all_prefix_nonneg and equal}")
        print()

if __name__ == "__main__":
    test_h_final_complex_case()
    test_individual_prefix_correspondence()