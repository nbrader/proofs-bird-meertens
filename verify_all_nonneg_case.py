#!/usr/bin/env python3
"""
Verify the all non-negative case:
When all elements are >= 0, nonNegSum xs should equal nonNegMaximum (map nonNegSum (inits xs))
and both should equal the sum of the entire list.
"""

def nonNegPlus(a, b):
    return max(0, a + b)

def nonNegSum(xs):
    result = 0
    for x in xs:
        result = nonNegPlus(x, result)
    return result

def inits(xs):
    """Generate all initial segments (prefixes) of xs"""
    result = [[]]  # empty list is always a prefix
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def nonNegMaximum(values):
    """Return maximum of values, or 0 if empty"""
    if not values:
        return 0
    return max(values)

def test_all_nonneg_case(xs, description=""):
    """Test the all non-negative case"""
    print(f"\n{description}")
    print(f"List: {xs}")

    # Check that all elements are non-negative
    all_nonneg = all(x >= 0 for x in xs)
    print(f"All non-negative: {all_nonneg}")

    if not all_nonneg:
        print("Skipping - not all non-negative")
        return

    # Compute nonNegSum of the entire list
    lhs = nonNegSum(xs)
    print(f"nonNegSum(xs): {lhs}")

    # Compute all prefix sums and their maximum
    prefixes = inits(xs)
    print(f"Prefixes: {prefixes}")

    prefix_sums = [nonNegSum(prefix) for prefix in prefixes]
    print(f"Prefix nonNegSums: {prefix_sums}")

    rhs = nonNegMaximum(prefix_sums)
    print(f"nonNegMaximum(prefix sums): {rhs}")

    # Check equality
    equal = lhs == rhs
    print(f"Equal: {equal}")

    # For all non-negative lists, nonNegSum should equal regular sum
    regular_sum = sum(xs)
    print(f"Regular sum: {regular_sum}")
    print(f"nonNegSum == regular sum: {lhs == regular_sum}")

    # The maximum prefix sum should be the entire list
    max_prefix_idx = prefix_sums.index(max(prefix_sums))
    print(f"Maximum achieved by prefix: {prefixes[max_prefix_idx]}")

    return equal

# Test cases
test_cases = [
    ([1, 2, 3], "Simple positive"),
    ([0, 0, 0], "All zeros"),
    ([5], "Single positive"),
    ([0], "Single zero"),
    ([], "Empty list"),
    ([1, 0, 2, 0, 3], "Mixed positive and zero"),
    ([2, 3, 1, 4], "Longer positive sequence"),
]

print("TESTING ALL NON-NEGATIVE CASE")
print("="*50)

all_pass = True
for xs, desc in test_cases:
    if not test_all_nonneg_case(xs, desc):
        all_pass = False

print(f"\n" + "="*50)
print(f"All tests pass: {all_pass}")

# Key insight for the proof
print("\nKEY INSIGHT FOR PROOF:")
print("When all elements are >= 0:")
print("1. nonNegSum behaves exactly like regular sum (no clamping)")
print("2. Each prefix sum is >= previous prefix sum (monotonic increase)")
print("3. Therefore maximum prefix sum is achieved by the entire list")
print("4. So nonNegSum(xs) = nonNegMaximum(map nonNegSum (inits xs))")