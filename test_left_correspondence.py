#!/usr/bin/env python3
"""
Test the left-side correspondence:
fold_right nonNegPlus 0 xs = n where fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 (map Finite xs) = Finite n

This tests our second admit: that n = fold_right nonNegPlus 0 xs
where the tropical operation produces Finite n.
"""

def nonNegPlus(x, y):
    return max(0, x + y)

def fold_right_nonNegPlus(xs):
    result = 0
    for x in reversed(xs):
        result = nonNegPlus(x, result)
    return result

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
    """Tropical addition (max operation)"""
    if x.is_neginf:
        return y
    elif y.is_neginf:
        return x
    else:
        return ExtZ(max(x.value, y.value))

def tropical_mul(x, y):
    """Tropical multiplication (regular addition)"""
    if x.is_neginf or y.is_neginf:
        return ExtZ(is_neginf=True)
    else:
        return ExtZ(x.value + y.value)

def tropical_one():
    """Tropical multiplicative identity"""
    return ExtZ(0)

def tropical_horner_step(x, y):
    """The step function: (x ⊗ y) ⊕ 𝟏"""
    return tropical_add(tropical_mul(x, y), tropical_one())

def fold_right_tropical(xs):
    """fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 xs"""
    result = tropical_one()  # 𝟏
    for x in reversed(xs):
        result = tropical_horner_step(x, result)
    return result

def map_finite(xs):
    """Map regular integers to Finite ExtZ values"""
    return [ExtZ(x) for x in xs]

def test_left_correspondence(xs):
    """Test that nonNegPlus result equals the value inside Finite tropical result"""
    # Left side: fold_right nonNegPlus 0 xs
    left_result = fold_right_nonNegPlus(xs)

    # Right side: extract n from fold_right tropical (map Finite xs) = Finite n
    finite_xs = map_finite(xs)
    tropical_result = fold_right_tropical(finite_xs)

    # The tropical result should be Finite n where n = left_result
    if tropical_result.is_neginf:
        right_result = 0  # This case shouldn't happen for finite inputs
        match = (left_result == 0)
    else:
        right_result = tropical_result.value
        match = (left_result == right_result)

    print(f"xs = {xs}")
    print(f"left_result (nonNegPlus) = {left_result}")
    print(f"tropical_result = {tropical_result}")
    print(f"right_result (extracted) = {right_result}")
    print(f"correspondence holds = {match}")
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
    [-5, 10, -3, 8, -2, 4],  # Mixed case
    [5, -15, 10, -8, 6]  # Another mixed case
]

print("Testing left-side correspondence:")
print("fold_right nonNegPlus 0 xs =?= n where fold_right tropical (map Finite xs) = Finite n")
print("=" * 85)

all_match = True
for xs in test_cases:
    match = test_left_correspondence(xs)
    if not match:
        all_match = False

print("=" * 85)
if all_match:
    print("✅ SUCCESS: All test cases show perfect correspondence!")
    print("Left-side correspondence (nonNegPlus ↔ tropical) is computationally verified.")
else:
    print("❌ FAILURE: Some test cases show correspondence mismatch.")
    print("The left-side correspondence does not hold universally.")

print(f"\nTested {len(test_cases)} cases, all match: {all_match}")

# Additional analysis: Show the relationship more explicitly
print("\nDetailed analysis of correspondence pattern:")
print("-" * 50)
for xs in [[1, -3, 2], [3, -5, 4, -2, 1], [-1, 3, -2]]:
    left = fold_right_nonNegPlus(xs)
    tropical = fold_right_tropical(map_finite(xs))

    print(f"xs = {xs}")
    print(f"  nonNegPlus result: {left}")
    print(f"  tropical result: {tropical}")

    if not tropical.is_neginf:
        print(f"  extracted value: {tropical.value}")
        print(f"  values equal: {left == tropical.value}")
    print()