#!/usr/bin/env python3
"""
Test script for the UPDATED admitted lemma at line 444 in Lemmas.v:

Lemma generalised_horners_rule : fold_right (fun x y : Z => x <#> y <|> 0) 0 = nonNegMaximum ∘ map nonNegSum ∘ inits.

With UPDATED definitions:
- nonNegSum (xs : list Z) : Z := fold_right nonNegPlus 0%Z xs  [CHANGED from fold_left]
- <#> is nonNegPlus: max(0, x + y)
- <|> is Z.max: max(x, y)
- inits returns all initial segments of a list
"""

import random
import sys

def non_neg_plus(x, y):
    """nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def z_max(x, y):
    """Z.max operation: max(x, y)"""
    return max(x, y)

def fold_right(op, initial, lst):
    """Haskell-style fold_right (foldr)"""
    if not lst:
        return initial
    return op(lst[0], fold_right(op, initial, lst[1:]))

def non_neg_sum_right(lst):
    """UPDATED nonNegSum using fold_right (not fold_left)"""
    return fold_right(non_neg_plus, 0, lst)

def non_neg_maximum(lst):
    """nonNegMaximum: fold_right z_max 0"""
    return fold_right(z_max, 0, lst)

def inits(lst):
    """All initial segments of a list"""
    return [lst[:i] for i in range(len(lst) + 1)]

def left_side_447_updated(lst):
    """
    Left side: fold_right (fun x y : Z => x <#> y <|> 0) 0

    This is a single fold_right with compound operation: (x <#> y) <|> 0
    """
    def compound_op(x, y):
        return z_max(non_neg_plus(x, y), 0)

    return fold_right(compound_op, 0, lst)

def right_side_447_updated(lst):
    """
    Right side: nonNegMaximum ∘ map nonNegSum ∘ inits

    Step by step:
    1. inits lst -> get all initial segments
    2. map nonNegSum -> fold each segment with nonNegPlus (using fold_right now!)
    3. nonNegMaximum -> fold the results with z_max
    """
    # Step 1: Get all initial segments
    initial_segments = inits(lst)

    # Step 2: Apply fold_right nonNegPlus 0 to each segment (UPDATED)
    folded_segments = [non_neg_sum_right(seg) for seg in initial_segments]

    # Step 3: Apply nonNegMaximum (fold_right z_max 0)
    return non_neg_maximum(folded_segments)

def test_lemma_447_updated(lst):
    """Test the updated lemma 447 on a specific list"""
    left = left_side_447_updated(lst)
    right = right_side_447_updated(lst)
    return left, right, left == right

def detailed_analysis_447_updated(lst):
    """Detailed step-by-step analysis"""
    print(f"Detailed analysis for updated lemma 447 with {lst}:")
    print("=" * 60)

    # LEFT SIDE
    print("LEFT SIDE:")
    print(f"  fold_right compound_op 0 {lst}")

    def trace_fold_right(lst, depth=0):
        indent = "  " * (depth + 1)
        if not lst:
            print(f"{indent}Base case: 0")
            return 0
        else:
            x = lst[0]
            remaining = lst[1:]
            print(f"{indent}compound_op({x}, fold_right(compound_op, 0, {remaining}))")
            y = trace_fold_right(remaining, depth + 1)
            result = z_max(non_neg_plus(x, y), 0)
            print(f"{indent}= z_max(non_neg_plus({x}, {y}), 0)")
            print(f"{indent}= z_max({non_neg_plus(x, y)}, 0) = {result}")
            return result

    left_result = trace_fold_right(lst)

    # RIGHT SIDE
    print("\nRIGHT SIDE:")
    initial_segments = inits(lst)
    print(f"  inits({lst}) = {initial_segments}")

    folded_segments = []
    for seg in initial_segments:
        seg_sum = non_neg_sum_right(seg)
        folded_segments.append(seg_sum)
        print(f"  fold_right nonNegPlus 0 {seg} = {seg_sum}")

    print(f"  Folded segments: {folded_segments}")
    right_result = non_neg_maximum(folded_segments)
    print(f"  nonNegMaximum {folded_segments} = {right_result}")

    print(f"\nRESULT:")
    print(f"  Left side:  {left_result}")
    print(f"  Right side: {right_result}")
    print(f"  Equal? {left_result == right_result}")

    return left_result == right_result

# Test cases
test_cases = [
    [],
    [1],
    [-1],
    [0],
    [1, 2],
    [-1, -2],
    [1, -1],
    [-3, 1, 1],
    [1, -2, 3],
    [0, 1],
    [1, 1],
    [2, 0],
    [1, 2, 3],
    [-1, -2, -3],
    [5, -3, -2],
    [-5, 3, 2],
    [1, -2, 3, -1, 2],
    [10, -5, 3, -2, 1],
    [0, 1, 0, -1, 2],
    [2, -3, 4, -1, 2, 1, -5, 4]
]

print("Testing UPDATED Admitted Lemma at Line 444 from Lemmas.v")
print("=" * 70)
print("Testing: fold_right (fun x y : Z => x <#> y <|> 0) 0")
print("       = nonNegMaximum ∘ map nonNegSum ∘ inits")
print("Where nonNegSum NOW uses fold_right (not fold_left)")
print("=" * 70)

print("\nTesting specific cases:")
print("-" * 40)

counterexamples = []
for case in test_cases:
    left, right, equal = test_lemma_447_updated(case)
    status = "✓" if equal else "✗"
    print(f"{status} {str(case):20} => L={left:3}, R={right:3}, equal={equal}")
    if not equal:
        counterexamples.append((case, left, right))

print(f"\nSummary:")
print(f"Total test cases: {len(test_cases)}")
print(f"Counterexamples found: {len(counterexamples)}")

if counterexamples:
    print(f"❌ Updated Lemma 447 FAILS for {len(counterexamples)} cases:")
    for case, left, right in counterexamples[:3]:  # Show first 3
        print(f"  {case}: left={left}, right={right}")
else:
    print("✅ Updated Lemma 447 HOLDS for all test cases!")

print("\n" + "=" * 70)
print("DETAILED ANALYSIS OF KEY CASES:")
print("=" * 70)

# Detailed analysis for a few key cases
key_cases = [[-3, 1, 1], [1, -2, 3], [0, 1], []]
for case in key_cases:
    print()
    detailed_analysis_447_updated(case)

# Random testing
print("\n" + "=" * 70)
print("RANDOM TESTING:")
print("=" * 70)

random.seed(42)
failures = 0
num_tests = 500

print(f"Running {num_tests} random tests...")
for i in range(num_tests):
    if (i + 1) % 100 == 0:
        print(f"  Progress: {i+1}/{num_tests}, {failures} failures so far")

    # Generate random list
    length = random.randint(0, 8)
    lst = [random.randint(-10, 10) for _ in range(length)]

    left, right, equal = test_lemma_447_updated(lst)
    if not equal:
        failures += 1

print(f"\nRandom test results:")
print(f"  Tests run: {num_tests}")
print(f"  Failures: {failures}")

print("\n" + "=" * 70)
print("FINAL CONCLUSION:")
print("=" * 70)

if failures == 0 and len(counterexamples) == 0:
    print("🎉 All tests passed! Updated Lemma 447 appears to be TRUE.")
    print("\nThis means the updated admitted lemma can likely be proven.")
else:
    print("❌ Tests failed! Updated Lemma 447 appears to be FALSE.")
    print(f"   Counterexamples: {len(counterexamples)} from specific tests")
    print(f"   Random failures: {failures}/{num_tests}")