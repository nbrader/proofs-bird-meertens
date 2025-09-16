#!/usr/bin/env python3
"""
Test script for the UPDATED admitted lemma at line 448 in Lemmas.v:

Lemma generalised_horners_rule' : nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec = nonNegMaximum ∘ map nonNegSum ∘ tails_rec.

With UPDATED definitions:
- nonNegSum (xs : list Z) : Z := fold_right nonNegPlus 0%Z xs  [CHANGED from fold_left]
- Uses generalised_horners_rule in the proof: rewrite <- generalised_horners_rule.
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

def tails_rec(lst):
    """Recursive definition of tails"""
    if not lst:
        return [[]]
    return [lst] + tails_rec(lst[1:])

def left_side_448_updated(lst):
    """
    Left side: nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec

    Step by step:
    1. tails_rec lst -> get all tails
    2. For each tail, apply: nonNegMaximum ∘ map nonNegSum ∘ inits
    3. nonNegMaximum of all results
    """
    # Step 1: Get all tails
    all_tails = tails_rec(lst)

    # Step 2: For each tail, apply the inner composition
    inner_results = []
    for tail in all_tails:
        # Apply: nonNegMaximum ∘ map nonNegSum ∘ inits
        tail_inits = inits(tail)
        tail_sums = [non_neg_sum_right(init) for init in tail_inits]
        tail_max = non_neg_maximum(tail_sums)
        inner_results.append(tail_max)

    # Step 3: nonNegMaximum of all results
    return non_neg_maximum(inner_results)

def right_side_448_updated(lst):
    """
    Right side: nonNegMaximum ∘ map nonNegSum ∘ tails_rec

    Step by step:
    1. tails_rec lst -> get all tails
    2. map nonNegSum -> apply nonNegSum to each tail (using fold_right now!)
    3. nonNegMaximum -> maximum of all results
    """
    # Step 1: Get all tails
    all_tails = tails_rec(lst)

    # Step 2: Apply nonNegSum to each tail (fold_right version)
    tail_sums = [non_neg_sum_right(tail) for tail in all_tails]

    # Step 3: nonNegMaximum of all results
    return non_neg_maximum(tail_sums)

def test_lemma_448_updated(lst):
    """Test the updated lemma 448 on a specific list"""
    left = left_side_448_updated(lst)
    right = right_side_448_updated(lst)
    return left, right, left == right

def detailed_analysis_448_updated(lst):
    """Detailed step-by-step analysis"""
    print(f"Detailed analysis for updated lemma 448 with {lst}:")
    print("=" * 60)

    all_tails = tails_rec(lst)
    print(f"tails_rec({lst}) = {all_tails}")

    print(f"\nComponent-wise analysis:")

    left_components = []
    right_components = []

    for i, tail in enumerate(all_tails):
        # Left side computation for this tail
        tail_inits = inits(tail)
        tail_sums = [non_neg_sum_right(init) for init in tail_inits]
        tail_max = non_neg_maximum(tail_sums)
        left_components.append(tail_max)

        # Right side computation for this tail
        tail_sum = non_neg_sum_right(tail)
        right_components.append(tail_sum)

        status = "✓" if tail_max == tail_sum else "✗"
        print(f"  {status} tail[{i}] = {tail}")
        print(f"     Left (max of prefix sums):  {tail_max}")
        print(f"     Right (total sum):          {tail_sum}")
        print(f"     Equal: {tail_max == tail_sum}")

    print(f"\nFinal computation:")
    print(f"  Left components:  {left_components}")
    print(f"  Right components: {right_components}")

    left_final = non_neg_maximum(left_components)
    right_final = non_neg_maximum(right_components)

    print(f"  nonNegMaximum(left):  {left_final}")
    print(f"  nonNegMaximum(right): {right_final}")
    print(f"  Full lemma holds? {left_final == right_final}")

    return left_final == right_final

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

print("Testing UPDATED Admitted Lemma at Line 448 from Lemmas.v")
print("=" * 70)
print("Testing: nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails_rec")
print("       = nonNegMaximum ∘ map nonNegSum ∘ tails_rec")
print("Where nonNegSum NOW uses fold_right (not fold_left)")
print("=" * 70)

print("\nTesting specific cases:")
print("-" * 40)

counterexamples = []
for case in test_cases:
    left, right, equal = test_lemma_448_updated(case)
    status = "✓" if equal else "✗"
    print(f"{status} {str(case):20} => L={left:3}, R={right:3}, equal={equal}")
    if not equal:
        counterexamples.append((case, left, right))

print(f"\nSummary:")
print(f"Total test cases: {len(test_cases)}")
print(f"Counterexamples found: {len(counterexamples)}")

if counterexamples:
    print(f"❌ Updated Lemma 448 FAILS for {len(counterexamples)} cases:")
    for case, left, right in counterexamples[:3]:  # Show first 3
        print(f"  {case}: left={left}, right={right}")
else:
    print("✅ Updated Lemma 448 HOLDS for all test cases!")

print("\n" + "=" * 70)
print("DETAILED ANALYSIS OF KEY CASES:")
print("=" * 70)

# Detailed analysis for a few key cases
key_cases = [[-3, 1, 1], [1, -2, 3], [0, 1], []]
for case in key_cases:
    print()
    detailed_analysis_448_updated(case)

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

    left, right, equal = test_lemma_448_updated(lst)
    if not equal:
        failures += 1

print(f"\nRandom test results:")
print(f"  Tests run: {num_tests}")
print(f"  Failures: {failures}")

print("\n" + "=" * 70)
print("FINAL CONCLUSION:")
print("=" * 70)

if failures == 0 and len(counterexamples) == 0:
    print("🎉 All tests passed! Updated Lemma 448 appears to be TRUE.")
    print("\nThis means the updated admitted lemma can likely be proven.")
else:
    print("❌ Tests failed! Updated Lemma 448 appears to be FALSE.")
    print(f"   Counterexamples: {len(counterexamples)} from specific tests")
    print(f"   Random failures: {failures}/{num_tests}")