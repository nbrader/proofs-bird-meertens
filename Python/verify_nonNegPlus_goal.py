#!/usr/bin/env python3
"""
Computational verification of the nonNegPlus_agrees_with_add_on_prefix goal.

Given hypotheses:
- H_sum_nonneg : 0 <= fold_right Z.add 0 (x :: p')  [x + sum(p') >= 0]
- H_p'_neg : ~ 0 <= fold_right Z.add 0 p'            [sum(p') < 0]
- H_nonneg_ge_zero : fold_right nonNegPlus 0 p' >= 0  [always true by definition]
- H_ge_add : fold_right Z.add 0 p' <= fold_right nonNegPlus 0 p'  [follows from nonNegPlus definition]
- H_final_nonneg : 0 <= x + fold_right nonNegPlus 0 p'  [x + nonNegSum(p') >= 0]

Goal: x + fold_right nonNegPlus 0 p' = x + fold_right Z.add 0 p'
"""

def nonNegPlus(x, y):
    """Coq nonNegPlus operation: max(0, x + y)"""
    return max(0, x + y)

def fold_right_nonNegPlus(lst):
    """fold_right nonNegPlus 0 lst"""
    result = 0
    for val in reversed(lst):
        result = nonNegPlus(val, result)
    return result

def fold_right_add(lst):
    """fold_right Z.add 0 lst = sum(lst)"""
    return sum(lst)

def check_hypotheses(x, p_prime):
    """Check if the given x and p' satisfy all hypotheses"""
    sum_p_prime = fold_right_add(p_prime)
    sum_x_p_prime = x + sum_p_prime
    nonneg_sum_p_prime = fold_right_nonNegPlus(p_prime)

    # Check each hypothesis
    H_sum_nonneg = (sum_x_p_prime >= 0)
    H_p_neg = (sum_p_prime < 0)  # NOT (sum_p_prime >= 0)
    H_nonneg_ge_zero = (nonneg_sum_p_prime >= 0)  # Always true by definition
    H_ge_add = (sum_p_prime <= nonneg_sum_p_prime)
    H_final_nonneg = (x + nonneg_sum_p_prime >= 0)

    return H_sum_nonneg and H_p_neg and H_nonneg_ge_zero and H_ge_add and H_final_nonneg

def check_goal(x, p_prime):
    """Check if the goal holds: x + nonNegSum(p') = x + sum(p')"""
    nonneg_sum_p_prime = fold_right_nonNegPlus(p_prime)
    sum_p_prime = fold_right_add(p_prime)

    lhs = x + nonneg_sum_p_prime
    rhs = x + sum_p_prime

    return lhs == rhs

def find_counterexamples():
    """Search for counterexamples where hypotheses hold but goal fails"""
    counterexamples = []

    print("Searching for examples where hypotheses hold...")

    # Test various combinations
    for x in range(-10, 11):
        for p_len in range(1, 5):  # Test lists of length 1-4
            # Generate some test lists with negative sums
            test_lists = [
                [-1] * p_len,  # All -1s
                [-2] * p_len,  # All -2s
                [-1, -3],      # Mixed negative
                [-5, 1],       # Mostly negative
                [-3, -1, 1],   # Mixed with small positive
                [-10, 2, 3],   # Large negative start
                [1, -5],       # Positive start, negative total
                [2, -8, 1],    # Complex mix
            ]

            for p_prime in test_lists:
                if len(p_prime) != p_len:
                    continue

                if check_hypotheses(x, p_prime):
                    goal_holds = check_goal(x, p_prime)

                    sum_p_prime = fold_right_add(p_prime)
                    nonneg_sum_p_prime = fold_right_nonNegPlus(p_prime)

                    print(f"\nFound valid example:")
                    print(f"  x = {x}, p' = {p_prime}")
                    print(f"  sum(p') = {sum_p_prime}")
                    print(f"  nonNegSum(p') = {nonneg_sum_p_prime}")
                    print(f"  x + sum(p') = {x + sum_p_prime}")
                    print(f"  x + nonNegSum(p') = {x + nonneg_sum_p_prime}")
                    print(f"  Goal holds: {goal_holds}")

                    if not goal_holds:
                        counterexamples.append((x, p_prime))
                        print(f"  *** COUNTEREXAMPLE FOUND! ***")

    return counterexamples

def analyze_specific_case():
    """Analyze a specific case that might reveal the issue"""
    print("\n" + "="*60)
    print("SPECIFIC CASE ANALYSIS")
    print("="*60)

    # Case where p' has negative sum but x compensates
    x = 5
    p_prime = [-2, -1]  # sum = -3, but x + sum = 2 >= 0

    print(f"Testing: x = {x}, p' = {p_prime}")

    sum_p_prime = fold_right_add(p_prime)
    nonneg_sum_p_prime = fold_right_nonNegPlus(p_prime)

    print(f"sum(p') = {sum_p_prime}")
    print(f"nonNegSum(p') calculation:")

    # Step by step nonNegSum calculation
    result = 0
    for i, val in enumerate(reversed(p_prime)):
        old_result = result
        result = nonNegPlus(val, result)
        print(f"  Step {i+1}: nonNegPlus({val}, {old_result}) = max(0, {val + old_result}) = {result}")

    print(f"Final nonNegSum(p') = {nonneg_sum_p_prime}")

    # Check hypotheses
    hypotheses_hold = check_hypotheses(x, p_prime)
    goal_holds = check_goal(x, p_prime)

    print(f"\nHypotheses check:")
    print(f"  H_sum_nonneg: {x} + {sum_p_prime} = {x + sum_p_prime} >= 0? {x + sum_p_prime >= 0}")
    print(f"  H_p'_neg: {sum_p_prime} < 0? {sum_p_prime < 0}")
    print(f"  H_nonneg_ge_zero: {nonneg_sum_p_prime} >= 0? {nonneg_sum_p_prime >= 0}")
    print(f"  H_ge_add: {sum_p_prime} <= {nonneg_sum_p_prime}? {sum_p_prime <= nonneg_sum_p_prime}")
    print(f"  H_final_nonneg: {x} + {nonneg_sum_p_prime} = {x + nonneg_sum_p_prime} >= 0? {x + nonneg_sum_p_prime >= 0}")
    print(f"  All hypotheses hold: {hypotheses_hold}")

    print(f"\nGoal check:")
    print(f"  LHS: x + nonNegSum(p') = {x} + {nonneg_sum_p_prime} = {x + nonneg_sum_p_prime}")
    print(f"  RHS: x + sum(p') = {x} + {sum_p_prime} = {x + sum_p_prime}")
    print(f"  Goal holds: {goal_holds}")

    if not goal_holds:
        diff = (x + nonneg_sum_p_prime) - (x + sum_p_prime)
        print(f"  Difference: {diff} = nonNegSum(p') - sum(p') = {nonneg_sum_p_prime} - {sum_p_prime} = {nonneg_sum_p_prime - sum_p_prime}")

def main():
    print("COMPUTATIONAL VERIFICATION: nonNegPlus_agrees_with_add_on_prefix")
    print("="*70)

    # First analyze the mathematical structure
    print("MATHEMATICAL ANALYSIS:")
    print("If sum(p') < 0 and nonNegSum(p') >= 0, then nonNegSum(p') > sum(p')")
    print("So the goal x + nonNegSum(p') = x + sum(p') would require nonNegSum(p') = sum(p')")
    print("But this contradicts nonNegSum(p') > sum(p') when sum(p') < 0")
    print()

    # Search for counterexamples
    counterexamples = find_counterexamples()

    # Analyze a specific case
    analyze_specific_case()

    print("\n" + "="*60)
    print("CONCLUSION")
    print("="*60)

    if counterexamples:
        print(f"Found {len(counterexamples)} counterexample(s) where:")
        print("- All hypotheses are satisfied")
        print("- But the goal does NOT hold")
        print("\nThis suggests the goal is not always true given these hypotheses.")
        print("The issue is fundamental: when p' has negative sum, nonNegPlus")
        print("clamps to 0, making nonNegSum(p') >= 0 > sum(p'), so equality fails.")
    else:
        print("No counterexamples found in the tested range.")
        print("However, this doesn't prove the goal is always true.")

    print("\nThe lemma statement may need revision or additional constraints.")

if __name__ == "__main__":
    main()