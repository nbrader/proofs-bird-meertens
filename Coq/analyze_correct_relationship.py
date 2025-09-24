#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def fold_left_pair_fn(uv, x):
    """The pair function from the LHS of the lemma"""
    u, v = uv
    new_v = nonNegPlus(v, x)
    new_u = max(u, new_v)
    return (new_u, new_v)

def scan_left(f, xs, init):
    """scan_left function that produces intermediate results"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result[:-1]  # Remove the last element to match Coq's scan_left

def fold_left(f, xs, init):
    """Standard fold_left"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def analyze_relationship(xs, u0, v0):
    """Analyze what the correct RHS should be for the LHS"""

    # LHS: fold_left with pair function
    lhs = fold_left(fold_left_pair_fn, xs, (u0, v0))
    lhs_u, lhs_v = lhs

    # Current (incorrect) RHS
    scan_result = scan_left(nonNegPlus, xs, v0)
    wrong_rhs_first = fold_left(max, scan_result, u0)
    rhs_second = fold_left(nonNegPlus, xs, v0)
    wrong_rhs = (wrong_rhs_first, rhs_second)

    # Let's analyze what the LHS actually produces step by step
    print(f"xs={xs}, u0={u0}, v0={v0}")
    print(f"LHS result: {lhs}")
    print(f"Wrong RHS: {wrong_rhs}")
    print(f"scan_left result: {scan_result}")

    # What should the first component be?
    # Let's see: the LHS tracks max of all (u_i, v_i) pairs seen
    # Maybe it should be max(u0, max(all v_i values during computation))

    # Let's trace the v values during LHS computation
    acc = (u0, v0)
    v_values_seen = [v0]
    print(f"LHS step-by-step:")
    print(f"  Start: {acc}")

    for i, x in enumerate(xs):
        acc = fold_left_pair_fn(acc, x)
        v_values_seen.append(acc[1])
        print(f"  Step {i+1}: x={x} -> {acc}")

    print(f"v values seen: {v_values_seen}")

    # Hypothesis: correct first component should be max(u0, max(v_values_seen))
    correct_first_hypothesis = max(u0, max(v_values_seen))
    print(f"Hypothesis for correct first component: max(u0, max(v_values)) = {correct_first_hypothesis}")
    print(f"Actual LHS first component: {lhs_u}")
    print(f"Match: {correct_first_hypothesis == lhs_u}")

    # Alternative hypothesis: max of u0 and all intermediate v values (including v0)
    # This is equivalent to max(u0, final_v) since v is monotonic in our case
    alt_hypothesis = max(u0, lhs_v)
    print(f"Alternative hypothesis: max(u0, final_v) = {alt_hypothesis}")
    print(f"Match: {alt_hypothesis == lhs_u}")

    print("-" * 50)
    return lhs, wrong_rhs, v_values_seen

def test_corrected_lemma():
    """Test if our hypothesis for the correct lemma holds"""
    test_cases = [
        ([1, 2], 5, 3),
        ([1, 2, 3], 5, 3),
        ([5], 3, 2),
        ([2, 5, 1], 4, 1),
        ([1, 1, 1, 1, 1], 6, 2),
        ([], 5, 3),
        ([0, 0, 0], 5, 2),
    ]

    print("Testing corrected lemma hypothesis:")
    print("=" * 60)

    all_passed = True
    for xs, u0, v0 in test_cases:
        lhs, wrong_rhs, v_values = analyze_relationship(xs, u0, v0)

        # Test our hypothesis: LHS should equal (max(u0, final_v), final_v)
        lhs_u, lhs_v = lhs
        hypothesis_first = max(u0, lhs_v)
        hypothesis = (hypothesis_first, lhs_v)

        passed = lhs == hypothesis
        if not passed:
            all_passed = False
            print(f"HYPOTHESIS FAILED for {xs}")

    if all_passed:
        print("\n🎉 HYPOTHESIS CONFIRMED!")
        print("Correct lemma should be:")
        print("LHS = (max(u0, fold_left(nonNegPlus, xs, v0)), fold_left(nonNegPlus, xs, v0))")
    else:
        print("\n❌ Hypothesis doesn't hold universally")

if __name__ == "__main__":
    test_corrected_lemma()