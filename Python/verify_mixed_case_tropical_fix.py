#!/usr/bin/env python3

def tropical_add(a, b):
    """Tropical addition = max operation"""
    if a is None:  # NegInf
        return b
    if b is None:  # NegInf
        return a
    return max(a, b)

def fold_right_tropical_add(xs, init=None):
    """fold_right tropical_add NegInf xs"""
    result = init
    for x in reversed(xs):
        result = tropical_add(x, result)
    return result

def nonneg_sum(xs):
    """fold_right nonNegPlus 0 xs"""
    def nonneg_plus(x, y):
        result = x + y
        return result if result >= 0 else 0

    result = 0
    for x in reversed(xs):
        result = nonneg_plus(x, result)
    return result

def inits(xs):
    """All initial segments of a list"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[:i])
    return result

def has_mixed_signs(xs):
    """Check if list has mixed signs (both positive and negative elements)"""
    if not xs:
        return False
    has_pos = any(x > 0 for x in xs)
    has_neg = any(x < 0 for x in xs)
    return has_pos and has_neg

def test_mixed_case_tropical_correspondence():
    """Test tropical correspondence specifically for mixed case inputs"""
    test_cases = [
        [-1, 2],      # mixed: max subarray [2] = 2 >= 0
        [-2, 3, 1],   # mixed: max subarray [3, 1] = 4 >= 0
        [1, -2, 4],   # mixed: max subarray [4] = 4 >= 0
        [-1, -1, 5],  # mixed: max subarray [5] = 5 >= 0
        [2, -5, 3],   # mixed: max subarray [3] = 3 >= 0
    ]

    print("Testing tropical correspondence for mixed case inputs:")
    print("Key insight: In mixed case, maximum subarray sum >= 0")
    print()

    for xs in test_cases:
        if not has_mixed_signs(xs):
            continue

        print(f"xs = {xs} (mixed signs)")

        # Calculate all subarray sums using inits/nonneg_sum
        inits_xs = inits(xs)
        nonneg_sums = [nonneg_sum(prefix) for prefix in inits_xs]
        max_nonneg_sum = max(nonneg_sums)

        print(f"  inits(xs) = {inits_xs}")
        print(f"  nonneg_sums = {nonneg_sums}")
        print(f"  max_nonneg_sum = {max_nonneg_sum}")
        print(f"  max_nonneg_sum >= 0: {max_nonneg_sum >= 0}")

        # Test the tropical correspondence that was problematic
        # LHS: fold_right tropical_add NegInf (map Finite nonneg_sums)
        tropical_result = fold_right_tropical_add(nonneg_sums, None)

        # RHS: Finite (fold_right Z.max 0 nonneg_sums)
        max_result = max([0] + nonneg_sums)

        print(f"  tropical_add result: {tropical_result}")
        print(f"  max result: {max_result}")

        # Key insight: If max_nonneg_sum >= 0, then tropical_result should equal max_result
        if max_nonneg_sum >= 0:
            # In this case, fold_right tropical_add NegInf should give the max of nonneg_sums
            # which equals max([0] + nonneg_sums) since max(nonneg_sums) >= 0
            expected_equal = (tropical_result == max_result)
            print(f"  Expected equal (since max >= 0): {expected_equal}")

            if tropical_result != max_result:
                print(f"  ISSUE: tropical_result = {tropical_result}, max_result = {max_result}")
                # Analyze why
                if tropical_result is None:
                    print(f"    Problem: tropical_result is NegInf, but we have non-negative sums!")
                    print(f"    This suggests an empty list case or all NegInf inputs")
                    print(f"    But nonneg_sums = {nonneg_sums} contains non-negative values")
        print()

def test_empty_sublist_handling():
    """Test how the empty sublist [] is handled in the mixed case"""
    print("Testing empty sublist handling in mixed case:")
    print()

    # In mixed case, inits(xs) always includes [] as first element
    # nonneg_sum([]) = 0
    # So the list we pass to tropical_add will always include 0

    test_cases = [
        [-1, 2],
        [1, -2, 3],
    ]

    for xs in test_cases:
        print(f"xs = {xs}")
        inits_xs = inits(xs)
        nonneg_sums = [nonneg_sum(prefix) for prefix in inits_xs]

        print(f"  inits(xs)[0] = {inits_xs[0]} (empty prefix)")
        print(f"  nonneg_sum([]) = {nonneg_sums[0]}")
        print(f"  All nonneg_sums: {nonneg_sums}")

        # Since nonneg_sums[0] = 0, we're never passing an empty list to tropical_add
        # We're passing [0, ...] to tropical_add
        tropical_result = fold_right_tropical_add(nonneg_sums, None)
        print(f"  tropical_add on {nonneg_sums}: {tropical_result}")
        print(f"  This should equal max({nonneg_sums}) = {max(nonneg_sums)}")
        print()

if __name__ == "__main__":
    test_mixed_case_tropical_correspondence()
    test_empty_sublist_handling()