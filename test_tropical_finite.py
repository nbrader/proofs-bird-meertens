#!/usr/bin/env python3
"""
Test the tropical finite result property:
"Finite inputs always produce Finite result in tropical semiring"

This tests our first admit: that fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 (map Finite xs)
always produces a Finite result, never NegInf.
"""

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

    def __eq__(self, other):
        if self.is_neginf and other.is_neginf:
            return True
        elif not self.is_neginf and not other.is_neginf:
            return self.value == other.value
        else:
            return False

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

def test_finite_preservation(xs):
    """Test that finite inputs always produce finite results"""
    finite_xs = map_finite(xs)
    result = fold_right_tropical(finite_xs)

    print(f"xs = {xs}")
    print(f"finite_xs = {finite_xs}")
    print(f"result = {result}")
    print(f"is_finite = {not result.is_neginf}")
    print()

    return not result.is_neginf

# Test cases covering various scenarios
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
    [-100, 200, -50, 75, -25]  # Mixed large values
]

print("Testing tropical finite result property:")
print("fold_right (fun x y => (x ⊗ y) ⊕ 𝟏) 𝟏 (map Finite xs) always produces Finite result")
print("=" * 80)

all_finite = True
for xs in test_cases:
    is_finite = test_finite_preservation(xs)
    if not is_finite:
        all_finite = False
        print(f"❌ FAILED: xs = {xs} produced NegInf!")

print("=" * 80)
if all_finite:
    print("✅ SUCCESS: All test cases produced Finite results!")
    print("This supports the claim that finite inputs always produce finite results.")
else:
    print("❌ FAILURE: Some test cases produced NegInf results.")
    print("The finite preservation property does not hold universally.")

print(f"\nTested {len(test_cases)} cases, all finite: {all_finite}")