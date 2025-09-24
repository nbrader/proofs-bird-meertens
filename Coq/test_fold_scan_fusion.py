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

def test_lemma(xs, u0, v0):
    """Test the fold_scan_fusion_pair_general lemma"""
    # Preconditions
    if not (u0 >= v0 and v0 >= 0):
        return None, None, f"Preconditions not met: u0={u0}, v0={v0}"

    # LHS: fold_left with pair function
    lhs = fold_left(fold_left_pair_fn, xs, (u0, v0))

    # RHS: pair of fold_left Z.max on scan_left and fold_left sum
    scan_result = scan_left(nonNegPlus, xs, v0)
    rhs_first = fold_left(max, scan_result, u0)
    rhs_second = fold_left(nonNegPlus, xs, v0)
    rhs = (rhs_first, rhs_second)

    return lhs, rhs, None

def run_tests():
    """Run various test cases"""
    test_cases = [
        # (xs, u0, v0, description)
        ([], 5, 3, "Empty list"),
        ([1], 5, 3, "Single element"),
        ([1, 2], 5, 3, "Two elements"),
        ([1, 2, 3], 5, 3, "Three elements"),
        ([2, -1, 3], 5, 2, "Mixed positive/negative"),
        ([1, 2, 3, 4], 10, 5, "Larger example"),
        ([5], 3, 2, "Case where v0 + x > u0"),  # This is my counterexample
        ([2, 5, 1], 4, 1, "Multi-step case"),
        ([-1, -2, 5], 3, 1, "Negative then positive"),
        ([0, 0, 0], 5, 2, "All zeros"),
        ([1, 1, 1, 1, 1], 6, 2, "All ones"),
    ]

    print("Testing fold_scan_fusion_pair_general lemma:")
    print("=" * 60)

    all_passed = True
    for xs, u0, v0, desc in test_cases:
        lhs, rhs, error = test_lemma(xs, u0, v0)

        if error:
            print(f"SKIP: {desc} - {error}")
            continue

        passed = lhs == rhs
        status = "PASS" if passed else "FAIL"

        print(f"{status}: {desc}")
        print(f"  xs={xs}, u0={u0}, v0={v0}")
        print(f"  LHS: {lhs}")
        print(f"  RHS: {rhs}")

        if not passed:
            all_passed = False
            print(f"  ERROR: LHS != RHS")

            # Debug: show intermediate steps for failed cases
            scan_result = scan_left(nonNegPlus, xs, v0)
            print(f"  Debug: scan_left result = {scan_result}")

            # Show step-by-step fold_left for LHS
            acc = (u0, v0)
            print(f"  Debug LHS steps: start with {acc}")
            for i, x in enumerate(xs):
                acc = fold_left_pair_fn(acc, x)
                print(f"    step {i+1}: x={x} -> {acc}")

        print()

    if all_passed:
        print("🎉 ALL TESTS PASSED! The lemma appears to be TRUE.")
    else:
        print("❌ Some tests failed. The lemma might be FALSE or have additional constraints.")

if __name__ == "__main__":
    run_tests()