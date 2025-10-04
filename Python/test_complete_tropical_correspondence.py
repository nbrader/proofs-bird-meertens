#!/usr/bin/env python3
"""
Comprehensive test of the complete tropical correspondence chain:

This verifies the complete chain of our tropical semiring proof:
1. fold_right nonNegPlus 0 xs  [original left side]
2. = match fold_right tropical_horner (map Finite xs) with Finite z => z  [left correspondence]
3. = match fold_right tropical_add (map tropical_sum (inits (map Finite xs))) with Finite z => z  [tropical Horner's rule]
4. = fold_right Z.max 0 (map nonNegPlus (inits xs))  [right correspondence - original right side]

This is the complete proof chain for our maxsegsum_mixed_case lemma.
"""

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
    return max([0] + xs) if xs else 0

def inits(xs):
    return [xs[:i] for i in range(len(xs) + 1)]

class ExtZ:
    def __init__(self, value=None, is_neginf=False):
        if is_neginf:
            self.is_neginf = True
            self.value = None
        else:
            self.is_neginf = False
            self.value = value

    def __repr__(self):
        return "NegInf" if self.is_neginf else f"Finite({self.value})"

def tropical_add(x, y):
    if x.is_neginf: return y
    elif y.is_neginf: return x
    else: return ExtZ(max(x.value, y.value))

def tropical_mul(x, y):
    if x.is_neginf or y.is_neginf: return ExtZ(is_neginf=True)
    else: return ExtZ(x.value + y.value)

def tropical_one():
    return ExtZ(0)

def tropical_zero():
    return ExtZ(is_neginf=True)

def tropical_horner_step(x, y):
    return tropical_add(tropical_mul(x, y), tropical_one())

def fold_right_tropical_horner(xs):
    result = tropical_one()
    for x in reversed(xs):
        result = tropical_horner_step(x, result)
    return result

def fold_right_tropical_add(xs):
    result = tropical_zero()
    for x in reversed(xs):
        result = tropical_add(x, result)
    return result

def fold_right_tropical_mul(xs):
    result = tropical_one()
    for x in reversed(xs):
        result = tropical_mul(x, result)
    return result

def map_finite(xs):
    return [ExtZ(x) for x in xs]

def extract_finite_value(ext_z):
    """Extract value from ExtZ, returning 0 for NegInf"""
    return 0 if ext_z.is_neginf else ext_z.value

def test_complete_correspondence(xs):
    """Test the complete correspondence chain"""
    print(f"Testing complete correspondence for xs = {xs}")
    print("-" * 60)

    # Step 1: Original left side
    step1 = fold_right_nonNegPlus(xs)
    print(f"Step 1 - fold_right nonNegPlus 0 xs = {step1}")

    # Step 2: Left correspondence via tropical horner
    finite_xs = map_finite(xs)
    tropical_horner_result = fold_right_tropical_horner(finite_xs)
    step2 = extract_finite_value(tropical_horner_result)
    print(f"Step 2 - tropical horner result = {tropical_horner_result}")
    print(f"Step 2 - extracted value = {step2}")

    # Step 3: Tropical Horner's rule (right side of horner rule)
    finite_inits = inits(finite_xs)
    tropical_sums = [fold_right_tropical_mul(init) for init in finite_inits]
    tropical_add_result = fold_right_tropical_add(tropical_sums)
    step3 = extract_finite_value(tropical_add_result)
    print(f"Step 3 - inits(map Finite xs) = {finite_inits}")
    print(f"Step 3 - tropical sums = {tropical_sums}")
    print(f"Step 3 - tropical add result = {tropical_add_result}")
    print(f"Step 3 - extracted value = {step3}")

    # Step 4: Right correspondence back to original operations
    xs_inits = inits(xs)
    nonNeg_mapped = [fold_right_nonNegPlus(init) for init in xs_inits]
    step4 = fold_right_max(nonNeg_mapped)
    print(f"Step 4 - inits(xs) = {xs_inits}")
    print(f"Step 4 - map nonNegPlus over inits = {nonNeg_mapped}")
    print(f"Step 4 - fold_right Z.max 0 result = {step4}")

    # Verify all steps match
    chain_valid = (step1 == step2 == step3 == step4)
    print(f"\nCorrespondence chain: {step1} = {step2} = {step3} = {step4}")
    print(f"Complete chain valid: {chain_valid}")

    # Also verify against our original relationship test
    original_right = fold_right_max([fold_right_add(init) for init in xs_inits])
    original_match = (step1 == original_right)
    print(f"Original relationship (from test_tropical_connection): {step1} = max of prefix sums = {original_right}")
    print(f"Original relationship holds: {original_match}")
    print()

    return chain_valid and original_match

# Test cases covering different scenarios
test_cases = [
    [],
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
    [-10, -5, 15, -8, 12],  # Mixed case
    [5, -10, 8, -3, 6, -4, 9]  # Complex mixed case
]

print("COMPREHENSIVE TROPICAL CORRESPONDENCE VERIFICATION")
print("=" * 80)
print("Testing complete chain:")
print("nonNegPlus → tropical horner → tropical Horner rule → Z.max correspondence")
print("=" * 80)

all_valid = True
for xs in test_cases:
    is_valid = test_complete_correspondence(xs)
    if not is_valid:
        all_valid = False
        print("❌ CHAIN BROKEN for xs =", xs)

print("=" * 80)
if all_valid:
    print("🎉 COMPLETE SUCCESS! 🎉")
    print("All correspondence steps verified computationally!")
    print("The tropical semiring approach is mathematically sound.")
    print("Our Coq proof framework is built on solid computational foundations.")
else:
    print("❌ FAILURE: Some correspondence chains are broken.")
    print("The tropical semiring approach needs refinement.")

print(f"\nTested {len(test_cases)} cases, all valid: {all_valid}")

# Final verification with the exact relationship we're proving
print("\nFINAL VERIFICATION - Exact theorem statement:")
print("∀ xs, nonNegSum xs = nonNegMaximum (map nonNegSum (inits xs))")
print("-" * 70)

for xs in [[1, -3, 2], [3, -5, 4, -2, 1], [-1, 3, -2]]:
    left = fold_right_nonNegPlus(xs)  # nonNegSum
    right = fold_right_max([fold_right_nonNegPlus(init) for init in inits(xs)])  # nonNegMaximum ∘ map nonNegSum ∘ inits

    print(f"xs = {xs}")
    print(f"  nonNegSum xs = {left}")
    print(f"  nonNegMaximum (map nonNegSum (inits xs)) = {right}")
    print(f"  equality holds: {left == right}")
    print()