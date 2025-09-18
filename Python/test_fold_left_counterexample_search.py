#!/usr/bin/env python3
"""
Systematic search for counterexamples to fold_left_combine_middle_assoc
when closure is NOT assumed.

This tests various operations to find cases where:
f (fold_left f xs x) (fold_left f ys y) ≠ fold_left f (xs ++ y :: ys) x

when the generating set is not closed under f.
"""

def fold_left(f, initial, lst):
    """Python implementation of fold_left"""
    result = initial
    for item in lst:
        result = f(result, item)
    return result

def test_systematic_counterexample_search():
    """Systematically search for counterexamples with various operations"""

    print("Systematic Search for Counterexamples")
    print("=" * 60)

    # Test 1: Subtraction (not associative, but let's see)
    def f_sub(a, b):
        return a - b

    print("Testing f(a,b) = a - b:")
    print("Checking middle associativity...")

    # Check middle associativity for small values
    middle_assoc_violations = []
    for a in range(-2, 3):
        for m in range(-2, 3):
            for b in range(-2, 3):
                left = f_sub(f_sub(a, m), b)
                right = f_sub(a, f_sub(m, b))
                if left != right:
                    middle_assoc_violations.append((a, m, b, left, right))

    print(f"Middle associativity violations: {len(middle_assoc_violations)}")
    if middle_assoc_violations:
        print("❌ Subtraction doesn't satisfy middle associativity - skip this test")
        print(f"Example: f(f({middle_assoc_violations[0][0]},{middle_assoc_violations[0][1]}),{middle_assoc_violations[0][2]}) = {middle_assoc_violations[0][3]} != {middle_assoc_violations[0][4]}")

    # Test 2: Custom operation - bounded addition
    def f_bounded_add(a, b):
        """Addition bounded at 3"""
        return min(a + b, 3)

    print(f"\nTesting f(a,b) = min(a + b, 3):")

    # Check middle associativity
    middle_assoc_ok = True
    for a in range(6):
        for m in range(6):
            for b in range(6):
                left = f_bounded_add(f_bounded_add(a, m), b)
                right = f_bounded_add(a, f_bounded_add(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")
                    break
            if not middle_assoc_ok:
                break
        if not middle_assoc_ok:
            break

    if middle_assoc_ok:
        print("✓ Bounded addition satisfies middle associativity")

        # Test with a generating set that's not closed
        gen_set = {0, 1}  # Not closed under bounded addition: min(1+1,3) = 2 ∉ {0,1}

        print(f"gen_set = {gen_set}")

        # Check closure violations
        violations = []
        for a in gen_set:
            for b in gen_set:
                result = f_bounded_add(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))

        print(f"Closure violations: {violations}")

        if violations:
            # Test the fold_left property
            test_cases = [
                ([1], [1], 0, 1),
                ([1, 1], [1], 0, 0),
                ([1], [1, 1], 1, 0),
            ]

            for xs, ys, x, y in test_cases:
                # Verify all elements are in gen_set
                all_elements = xs + ys + [x, y]
                if not all(elem in gen_set for elem in all_elements):
                    continue

                print(f"\nTesting: xs={xs}, ys={ys}, x={x}, y={y}")

                # Left side: f (fold_left f xs x) (fold_left f ys y)
                left_fold_xs = fold_left(f_bounded_add, x, xs)
                left_fold_ys = fold_left(f_bounded_add, y, ys)
                left_side = f_bounded_add(left_fold_xs, left_fold_ys)

                # Right side: fold_left f (xs ++ y :: ys) x
                combined_list = xs + [y] + ys
                right_side = fold_left(f_bounded_add, x, combined_list)

                print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
                print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
                print(f"  Left side:  f({left_fold_xs}, {left_fold_ys}) = {left_side}")
                print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")
                print(f"  Equal: {left_side == right_side}")

                # Check intermediate values
                intermediate_values = [left_fold_xs, left_fold_ys]
                outside_gen_set = [v for v in intermediate_values if v not in gen_set]

                if outside_gen_set:
                    print(f"  ⚠️  Intermediate values outside gen_set: {outside_gen_set}")

                if left_side != right_side:
                    print(f"  🎯 COUNTEREXAMPLE FOUND!")
                    return (xs, ys, x, y, left_side, right_side)
    else:
        print("❌ Bounded addition doesn't satisfy middle associativity")

def test_modular_operations():
    """Test with modular arithmetic operations"""

    print(f"\n" + "=" * 60)
    print("Testing Modular Operations")
    print("=" * 60)

    # Test modular multiplication
    def f_mult_mod5(a, b):
        return (a * b) % 5

    print("Testing f(a,b) = (a * b) mod 5:")

    # Check middle associativity
    middle_assoc_ok = True
    for a in range(5):
        for m in range(5):
            for b in range(5):
                left = f_mult_mod5(f_mult_mod5(a, m), b)
                right = f_mult_mod5(a, f_mult_mod5(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: ({a}*{m})*{b} mod 5 = {left} != {right} = {a}*({m}*{b}) mod 5")
                    break
            if not middle_assoc_ok:
                break
        if not middle_assoc_ok:
            break

    if middle_assoc_ok:
        print("✓ Modular multiplication satisfies middle associativity")

        # Use a generating set that's not closed under multiplication mod 5
        gen_set = {1, 2}  # 2*2 = 4 mod 5, so not closed

        print(f"gen_set = {gen_set}")

        # Check closure
        violations = []
        for a in gen_set:
            for b in gen_set:
                result = f_mult_mod5(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))

        print(f"Closure violations: {violations}")

        if violations:
            # Test cases
            test_cases = [
                ([2], [2], 1, 1),
                ([2, 2], [1], 1, 2),
            ]

            for xs, ys, x, y in test_cases:
                all_elements = xs + ys + [x, y]
                if not all(elem in gen_set for elem in all_elements):
                    continue

                print(f"\nTesting: xs={xs}, ys={ys}, x={x}, y={y}")

                left_fold_xs = fold_left(f_mult_mod5, x, xs)
                left_fold_ys = fold_left(f_mult_mod5, y, ys)
                left_side = f_mult_mod5(left_fold_xs, left_fold_ys)

                combined_list = xs + [y] + ys
                right_side = fold_left(f_mult_mod5, x, combined_list)

                print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
                print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
                print(f"  Left side:  ({left_fold_xs} * {left_fold_ys}) mod 5 = {left_side}")
                print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")
                print(f"  Equal: {left_side == right_side}")

                intermediate_values = [left_fold_xs, left_fold_ys]
                outside_gen_set = [v for v in intermediate_values if v not in gen_set]

                if outside_gen_set:
                    print(f"  ⚠️  Intermediate values outside gen_set: {outside_gen_set}")

                if left_side != right_side:
                    print(f"  🎯 COUNTEREXAMPLE FOUND!")
                    return (xs, ys, x, y, left_side, right_side)

    return None

def test_custom_middle_associative_operation():
    """Test with a custom operation designed to break without closure"""

    print(f"\n" + "=" * 60)
    print("Testing Custom Non-Closed Operation")
    print("=" * 60)

    # Custom operation: if both inputs are in {0,1}, return their max + 1
    # Otherwise, return the normal max
    def f_custom(a, b):
        if a in {0, 1} and b in {0, 1}:
            return max(a, b) + 1  # This takes us outside {0,1}
        else:
            return max(a, b)

    print("Testing custom f(a,b):")
    print("  if a,b ∈ {0,1}: f(a,b) = max(a,b) + 1")
    print("  otherwise: f(a,b) = max(a,b)")

    # Check middle associativity for relevant values
    test_values = [0, 1, 2, 3]
    middle_assoc_ok = True

    for a in test_values:
        for m in test_values:
            for b in test_values:
                left = f_custom(f_custom(a, m), b)
                right = f_custom(a, f_custom(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")
                    break
            if not middle_assoc_ok:
                break
        if not middle_assoc_ok:
            break

    if middle_assoc_ok:
        print("✓ Custom operation satisfies middle associativity")

        gen_set = {0, 1}
        print(f"gen_set = {gen_set}")

        # Check closure
        violations = []
        for a in gen_set:
            for b in gen_set:
                result = f_custom(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))

        print(f"Closure violations: {violations}")

        if violations:
            # Test the property
            test_cases = [
                ([1], [0], 0, 1),
                ([0], [1], 1, 0),
                ([1, 0], [1], 0, 1),
            ]

            for xs, ys, x, y in test_cases:
                all_elements = xs + ys + [x, y]
                if not all(elem in gen_set for elem in all_elements):
                    continue

                print(f"\nTesting: xs={xs}, ys={ys}, x={x}, y={y}")

                left_fold_xs = fold_left(f_custom, x, xs)
                left_fold_ys = fold_left(f_custom, y, ys)
                left_side = f_custom(left_fold_xs, left_fold_ys)

                combined_list = xs + [y] + ys
                right_side = fold_left(f_custom, x, combined_list)

                print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
                print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
                print(f"  Left side:  f({left_fold_xs}, {left_fold_ys}) = {left_side}")
                print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")
                print(f"  Equal: {left_side == right_side}")

                intermediate_values = [left_fold_xs, left_fold_ys]
                outside_gen_set = [v for v in intermediate_values if v not in gen_set]

                if outside_gen_set:
                    print(f"  ⚠️  Intermediate values outside gen_set: {outside_gen_set}")

                if left_side != right_side:
                    print(f"  🎯 COUNTEREXAMPLE FOUND!")
                    return (xs, ys, x, y, left_side, right_side)
    else:
        print("❌ Custom operation doesn't satisfy middle associativity")

    return None

if __name__ == "__main__":
    print("Searching for concrete counterexamples...")
    print("=" * 60)

    counterexample1 = test_systematic_counterexample_search()
    counterexample2 = test_modular_operations()
    counterexample3 = test_custom_middle_associative_operation()

    print("\n" + "=" * 60)
    print("SEARCH RESULTS")
    print("=" * 60)

    counterexamples = [ce for ce in [counterexample1, counterexample2, counterexample3] if ce is not None]

    if counterexamples:
        print(f"🎯 Found {len(counterexamples)} concrete counterexample(s)!")
        for i, ce in enumerate(counterexamples, 1):
            xs, ys, x, y, left, right = ce
            print(f"  {i}. xs={xs}, ys={ys}, x={x}, y={y} => {left} != {right}")
        print("\nThis proves that closure is REQUIRED for the property to hold!")
    else:
        print("🤔 No concrete counterexamples found with these operations.")
        print("The property appears to hold even without closure for these specific cases.")
        print("However, the PROOF STRUCTURE still requires closure as shown in the logical analysis.")

    print("\nKey insight: Even if computational counterexamples are rare,")
    print("the closure assumption is still logically necessary for the proof methodology.")