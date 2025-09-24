#!/usr/bin/env python3
"""
Test the right-side correspondence:
fold_right Z.max 0 (map (fold_right nonNegPlus 0) (inits xs)) =
z where fold_right add_op add_zero (map (fold_right mul_op mul_one) (inits (map Finite xs))) = Finite z

This tests our third admit: the correspondence between regular Z.max operations
and tropical semiring operations on the right side of the equation.
"""

def nonNegPlus(x, y):
    return max(0, x + y)

def fold_right_nonNegPlus(xs):
    result = 0
    for x in reversed(xs):
        result = nonNegPlus(x, result)
    return result

def fold_right_add(xs):
    """Regular addition fold_right"""
    return sum(xs)

def fold_right_max(xs):
    """Z.max fold_right with base case 0"""
    return max([0] + xs) if xs else 0

def inits(xs):
    """All initial segments of xs"""
    return [xs[:i] for i in range(len(xs) + 1)]

class ExtZ:
    """Extended integers with negative infinity for tropical semiring"""
    def __init__(self, value=None, is_neginf=False):
        if is_neginf:
            self.is_neginf = True
            self.value = None
        else:
            self.is_neginf = False
            self.value = value

    def __repr__(self):
        if self.is_neginf:
            return "NegInf"
        else:
            return f"Finite({self.value})"

def tropical_add(x, y):
    """Tropical addition (max operation) - add_op"""
    if x.is_neginf:
        return y
    elif y.is_neginf:
        return x
    else:
        return ExtZ(max(x.value, y.value))

def tropical_mul(x, y):
    """Tropical multiplication (regular addition) - mul_op"""
    if x.is_neginf or y.is_neginf:
        return ExtZ(is_neginf=True)
    else:
        return ExtZ(x.value + y.value)

def tropical_zero():
    """Tropical additive identity - add_zero"""
    return ExtZ(is_neginf=True)

def tropical_one():
    """Tropical multiplicative identity - mul_one"""
    return ExtZ(0)

def fold_right_tropical_add(xs):
    """fold_right add_op add_zero xs"""
    result = tropical_zero()
    for x in reversed(xs):
        result = tropical_add(x, result)
    return result

def fold_right_tropical_mul(xs):
    """fold_right mul_op mul_one xs"""
    result = tropical_one()
    for x in reversed(xs):
        result = tropical_mul(x, result)
    return result

def map_finite(xs):
    """Map regular integers to Finite ExtZ values"""
    return [ExtZ(x) for x in xs]

def test_right_correspondence(xs):
    """Test the right-side correspondence"""
    print(f"Testing xs = {xs}")

    # Left side: fold_right Z.max 0 (map (fold_right nonNegPlus 0) (inits xs))
    xs_inits = inits(xs)
    left_mapped = [fold_right_nonNegPlus(init) for init in xs_inits]
    left_result = fold_right_max(left_mapped)

    print(f"  inits(xs) = {xs_inits}")
    print(f"  map nonNegPlus over inits = {left_mapped}")
    print(f"  left_result (max) = {left_result}")

    # Right side: extract from fold_right add_op add_zero (map (fold_right mul_op mul_one) (inits (map Finite xs)))
    finite_xs = map_finite(xs)
    finite_inits = inits(finite_xs)

    print(f"  map Finite xs = {finite_xs}")
    print(f"  inits(map Finite xs) = {finite_inits}")

    # Apply fold_right mul_op mul_one to each init
    right_mapped = [fold_right_tropical_mul(init) for init in finite_inits]
    print(f"  map (fold_right mul_op mul_one) over inits = {right_mapped}")

    # Apply fold_right add_op add_zero to the mapped results
    tropical_result = fold_right_tropical_add(right_mapped)
    print(f"  tropical_result = {tropical_result}")

    # Extract the value for comparison
    if tropical_result.is_neginf:
        right_result = 0  # According to our correspondence, NegInf maps to 0
    else:
        right_result = tropical_result.value

    print(f"  right_result (extracted) = {right_result}")

    # Check correspondence
    match = (left_result == right_result)
    print(f"  correspondence holds = {match}")
    print()

    return match

# Test cases including various scenarios
test_cases = [
    [],
    [0],
    [1],
    [-1],
    [1, 2],
    [1, -2],
    [-1, 2],
    [-1, -2],
    [1, 2, 3],
    [1, -3, 2],
    [-1, 3, -2],
    [3, -5, 4, -2, 1],
    [-10, -20, -30],  # All negative
    [10, 20, 30],     # All positive
    [0, 0, 0],        # All zeros
]

print("Testing right-side correspondence:")
print("fold_right Z.max 0 (map nonNegPlus (inits xs)) =?= extracted from tropical operations")
print("=" * 90)

all_match = True
for xs in test_cases:
    match = test_right_correspondence(xs)
    if not match:
        all_match = False

print("=" * 90)
if all_match:
    print("✅ SUCCESS: All test cases show perfect right-side correspondence!")
    print("Right-side correspondence (Z.max ↔ tropical) is computationally verified.")
else:
    print("❌ FAILURE: Some test cases show correspondence mismatch.")
    print("The right-side correspondence does not hold universally.")

print(f"\nTested {len(test_cases)} cases, all match: {all_match}")

# Show that both sides compute the same fundamental result
print("\nVerification: Both sides compute maximum subarray sum:")
print("-" * 55)
for xs in [[1, -3, 2], [3, -5, 4, -2, 1]]:
    xs_inits = inits(xs)
    left_mapped = [fold_right_nonNegPlus(init) for init in xs_inits]
    max_subarray_sum = max(left_mapped)

    print(f"xs = {xs}")
    print(f"  all prefix sums: {[sum(init) for init in xs_inits]}")
    print(f"  all nonNegPlus results: {left_mapped}")
    print(f"  maximum (answer): {max_subarray_sum}")
    print()