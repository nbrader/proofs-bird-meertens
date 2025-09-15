#!/usr/bin/env python3
"""
Test script to verify whether form5 = form6 using the same definitions as in the Coq proof.
This tests the hypothesis that form5 and form6 might be equal despite the false generalized Horner's rule.
"""

def non_neg_plus(x, y):
    """nonNegPlus: adds x and y, returns 0 if result is negative"""
    return max(0, x + y)

def non_neg_sum(lst):
    """nonNegSum: fold using nonNegPlus"""
    result = 0
    for x in lst:
        result = non_neg_plus(x, result)
    return result

def non_neg_sum_right(lst):
    """nonNegSum using fold_right (Haskell-style foldr)"""
    if not lst:
        return 0
    return non_neg_plus(lst[0], non_neg_sum_right(lst[1:]))

def non_neg_maximum(lst):
    """nonNegMaximum: maximum of a list (assuming non-empty)"""
    if not lst:
        return 0  # Handle empty list case
    return max(lst)

def inits(lst):
    """All initial segments of a list"""
    return [lst[:i] for i in range(len(lst) + 1)]

def tails(lst):
    """All tail segments of a list"""
    return [lst[i:] for i in range(len(lst) + 1)]

def form5(lst):
    """form5: nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails"""
    tails_lst = tails(lst)
    mapped = []
    for tail in tails_lst:
        inits_tail = inits(tail)
        sums = [non_neg_sum(init) for init in inits_tail]
        max_sum = non_neg_maximum(sums)
        mapped.append(max_sum)
    return non_neg_maximum(mapped)

def form6(lst):
    """form6: nonNegMaximum ∘ map (foldr nonNegPlus 0) ∘ tails_rec"""
    # Note: tails_rec = tails in our implementation
    # IMPORTANT: Must use fold_right (foldr) as in the Coq definition
    tails_lst = tails(lst)
    mapped = [non_neg_sum_right(tail) for tail in tails_lst]
    return non_neg_maximum(mapped)

def test_generalized_horners_rule(lst):
    """Test the inner generalized Horner's rule for a specific list"""
    inner_form5 = non_neg_maximum([non_neg_sum(init) for init in inits(lst)])
    inner_form6 = non_neg_sum(lst)
    return inner_form5, inner_form6, inner_form5 == inner_form6

def test_forms(lst):
    """Test form5 vs form6 for a specific list"""
    f5 = form5(lst)
    f6 = form6(lst)
    return f5, f6, f5 == f6

def detailed_computation(lst):
    """Show detailed step-by-step computation"""
    print(f"\nDetailed computation for {lst}:")

    print(f"  tails({lst}) = {tails(lst)}")

    print("\n  Form5 computation:")
    tails_lst = tails(lst)
    form5_components = []
    for i, tail in enumerate(tails_lst):
        inits_tail = inits(tail)
        sums = [non_neg_sum(init) for init in inits_tail]
        max_sum = non_neg_maximum(sums)
        print(f"    tail[{i}] = {tail}")
        print(f"      inits = {inits_tail}")
        print(f"      nonNegSums = {sums}")
        print(f"      max = {max_sum}")
        form5_components.append(max_sum)
    f5_result = non_neg_maximum(form5_components)
    print(f"    final components = {form5_components}")
    print(f"    form5 result = {f5_result}")

    print("\n  Form6 computation (using fold_right):")
    form6_components = []
    for i, tail in enumerate(tails_lst):
        tail_sum = non_neg_sum_right(tail)  # Use fold_right
        print(f"    tail[{i}] = {tail} => nonNegSum_right = {tail_sum}")
        form6_components.append(tail_sum)
    f6_result = non_neg_maximum(form6_components)
    print(f"    final components = {form6_components}")
    print(f"    form6 result = {f6_result}")

    return f5_result, f6_result

def main():
    # Test cases
    test_cases = [
        [-3, 1, 1],        # The counterexample from generalised_horners_rule_is_false
        [],                # Empty list
        [1],               # Single element
        [1, 1],            # Two positive elements
        [-1, -1],          # Two negative elements
        [0, 1],            # Start with zero
        [2, 0],            # End with zero
        [1, -2, 3],        # Mixed positive/negative
        [-5, 3, 2],        # Start negative
        [5, -3, -2],       # End negative
        [1, 2, 3, 4, 5],   # All positive
        [-1, -2, -3],      # All negative
        [0, 0, 0],         # All zeros
        [10, -5, 3, -2, 1] # Longer mixed list
    ]

    print("Testing form5 vs form6 on various inputs:")
    print("=" * 50)

    counterexamples = []

    for lst in test_cases:
        f5, f6, equal = test_forms(lst)
        status = "✓" if equal else "✗"
        print(f"{status} {str(lst):20} => form5={f5:3}, form6={f6:3}, equal={equal}")

        if not equal:
            counterexamples.append(lst)

    print(f"\nSummary:")
    print(f"Total test cases: {len(test_cases)}")
    print(f"Counterexamples found: {len(counterexamples)}")

    if counterexamples:
        print(f"form5 ≠ form6 for: {counterexamples}")
    else:
        print("form5 = form6 for all test cases!")

    # Test the specific counterexample in detail
    print("\n" + "=" * 50)
    print("DETAILED ANALYSIS OF [-3, 1, 1]:")
    print("=" * 50)

    test_list = [-3, 1, 1]

    # Test the inner generalized Horner's rule
    inner5, inner6, inner_equal = test_generalized_horners_rule(test_list)
    inner6_right = non_neg_sum_right(test_list)

    print(f"Inner generalized Horner's rule for {test_list}:")
    print(f"  nonNegMaximum(map nonNegSum (inits {test_list})) = {inner5}")
    print(f"  nonNegSum({test_list}) [fold_left] = {inner6}")
    print(f"  nonNegSum({test_list}) [fold_right] = {inner6_right}")
    print(f"  Inner functions equal (fold_left)? {inner_equal}")
    print(f"  Inner functions equal (fold_right)? {inner5 == inner6_right}")

    # Let's test the exact computation from the Coq proof
    print(f"\n  Step-by-step computation:")
    print(f"    inits({test_list}) = {inits(test_list)}")
    inits_sums = [non_neg_sum(init) for init in inits(test_list)]
    print(f"    map nonNegSum = {inits_sums}")
    print(f"    maximum = {max(inits_sums)}")

    print(f"\n    fold_right nonNegPlus 0 {test_list}:")
    if test_list == [-3, 1, 1]:
        print(f"      1 `nonNegPlus` 0 = max(0, 1+0) = 1")
        print(f"      1 `nonNegPlus` 1 = max(0, 1+1) = 2")
        print(f"      (-3) `nonNegPlus` 2 = max(0, -3+2) = 0")
        print(f"      Result: 0")
    else:
        def step_by_step_fold_right(lst):
            if not lst:
                return 0
            if len(lst) == 1:
                return non_neg_plus(lst[0], 0)
            else:
                rest = step_by_step_fold_right(lst[1:])
                result = non_neg_plus(lst[0], rest)
                print(f"        {lst[0]} `nonNegPlus` {rest} = max(0, {lst[0]}+{rest}) = {result}")
                return result
        step_by_step_fold_right(test_list)

    # Detailed computation
    f5, f6 = detailed_computation(test_list)
    print(f"\nFinal comparison: form5 = {f5}, form6 = {f6}, equal = {f5 == f6}")

if __name__ == "__main__":
    main()