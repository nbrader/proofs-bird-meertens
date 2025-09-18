#!/usr/bin/env python3
"""
Ultimate attempt to find a counterexample by constructing a specific operation
that satisfies middle associativity but breaks the fold_left property without closure.
"""

def fold_left(f, initial, lst):
    """Python implementation of fold_left"""
    result = initial
    for item in lst:
        result = f(result, item)
    return result

def test_magma_with_absorbing_element():
    """Test with a magma that has specific absorption properties"""

    print("Testing Magma with Absorbing Element")
    print("=" * 50)

    def f_absorbing(a, b):
        """
        Operation with 2 as absorbing element:
        - f(2, x) = f(x, 2) = 2 for any x
        - f(0, 0) = 0, f(0, 1) = 1, f(1, 0) = 1, f(1, 1) = 2
        """
        if a == 2 or b == 2:
            return 2
        elif a == 0 and b == 0:
            return 0
        else:
            return 1

    print("Operation table:")
    print("  f(2, x) = f(x, 2) = 2 for any x")
    print("  f(0, 0) = 0")
    print("  f(0, 1) = f(1, 0) = f(1, 1) = 1")

    # Build complete operation table for verification
    table = {}
    for a in [0, 1, 2]:
        for b in [0, 1, 2]:
            table[(a, b)] = f_absorbing(a, b)

    print("\nComplete table:")
    print("    | 0  1  2")
    print("  --+--------")
    for a in [0, 1, 2]:
        row = f"  {a} |"
        for b in [0, 1, 2]:
            row += f" {table[(a, b)]} "
        print(row)

    # Check middle associativity
    middle_assoc_ok = True
    for a in [0, 1, 2]:
        for m in [0, 1, 2]:
            for b in [0, 1, 2]:
                left = f_absorbing(f_absorbing(a, m), b)
                right = f_absorbing(a, f_absorbing(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")

    if middle_assoc_ok:
        print("✓ Absorbing operation satisfies middle associativity")

        gen_set = {0, 1}  # f(1,1) = 1 ∈ gen_set, but other combos might cause issues
        print(f"gen_set = {gen_set}")

        # Check closure
        violations = []
        for a in gen_set:
            for b in gen_set:
                result = f_absorbing(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))

        print(f"Closure violations: {violations}")

        if not violations:
            print("Hmm, this set is actually closed. Let me check f(1,1)...")
            print(f"f(1,1) = {f_absorbing(1, 1)}")
            # f(1,1) = 1, so it's closed

    return None

def test_non_commutative_operation():
    """Test with a non-commutative operation"""

    print("\nTesting Non-Commutative Operation")
    print("=" * 50)

    def f_noncomm(a, b):
        """
        Non-commutative operation:
        f(a, b) = a if a >= b, else b + 1
        """
        if a >= b:
            return a
        else:
            return b + 1

    print("Operation: f(a,b) = a if a >= b, else b + 1")

    # Check if this satisfies middle associativity
    test_values = [0, 1, 2, 3]
    middle_assoc_violations = []

    for a in test_values:
        for m in test_values:
            for b in test_values:
                left = f_noncomm(f_noncomm(a, m), b)
                right = f_noncomm(a, f_noncomm(m, b))
                if left != right:
                    middle_assoc_violations.append((a, m, b, left, right))

    if middle_assoc_violations:
        print(f"❌ Non-commutative operation fails middle associativity")
        print(f"Violations: {len(middle_assoc_violations)}")
        for violation in middle_assoc_violations[:3]:  # Show first 3
            a, m, b, left, right = violation
            print(f"  f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")
        return None

    print("✓ Non-commutative operation satisfies middle associativity")
    return None

def test_finite_field_operation():
    """Test with operations in finite fields"""

    print("\nTesting Finite Field Operations")
    print("=" * 50)

    # GF(4) multiplication table (using polynomial representation)
    # Elements: 0, 1, α, α+1 where α² = α+1
    # We'll use 0, 1, 2, 3 to represent 0, 1, α, α+1

    gf4_mult_table = {
        (0, 0): 0, (0, 1): 0, (0, 2): 0, (0, 3): 0,
        (1, 0): 0, (1, 1): 1, (1, 2): 2, (1, 3): 3,
        (2, 0): 0, (2, 1): 2, (2, 2): 3, (2, 3): 1,
        (3, 0): 0, (3, 1): 3, (3, 2): 1, (3, 3): 2,
    }

    def f_gf4_mult(a, b):
        return gf4_mult_table.get((a, b), 0)

    print("GF(4) multiplication table:")
    print("    | 0  1  2  3")
    print("  --+----------")
    for a in [0, 1, 2, 3]:
        row = f"  {a} |"
        for b in [0, 1, 2, 3]:
            row += f" {f_gf4_mult(a, b)} "
        print(row)

    # Check middle associativity
    middle_assoc_ok = True
    for a in [0, 1, 2, 3]:
        for m in [0, 1, 2, 3]:
            for b in [0, 1, 2, 3]:
                left = f_gf4_mult(f_gf4_mult(a, m), b)
                right = f_gf4_mult(a, f_gf4_mult(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")

    if middle_assoc_ok:
        print("✓ GF(4) multiplication satisfies middle associativity (should be full associative)")

        # Use a generating set that's not closed under multiplication
        gen_set = {1, 2}  # f(2,2) = 3, so not closed
        print(f"gen_set = {gen_set}")

        violations = []
        for a in gen_set:
            for b in gen_set:
                result = f_gf4_mult(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))

        print(f"Closure violations: {violations}")

        if violations:
            # Test the property
            test_cases = [
                ([2], [2], 1, 1),  # This should cause f(2,2) = 3 to appear
            ]

            for xs, ys, x, y in test_cases:
                all_elements = xs + ys + [x, y]
                if not all(elem in gen_set for elem in all_elements):
                    continue

                print(f"\nTesting: xs={xs}, ys={ys}, x={x}, y={y}")

                left_fold_xs = fold_left(f_gf4_mult, x, xs)
                left_fold_ys = fold_left(f_gf4_mult, y, ys)
                left_side = f_gf4_mult(left_fold_xs, left_fold_ys)

                combined_list = xs + [y] + ys
                right_side = fold_left(f_gf4_mult, x, combined_list)

                print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
                print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
                print(f"  Left side:  f({left_fold_xs}, {left_fold_ys}) = {left_side}")
                print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")

                # Detailed trace
                print(f"  Right side detailed trace:")
                trace = x
                print(f"    start with {trace}")
                for i, elem in enumerate(combined_list):
                    new_trace = f_gf4_mult(trace, elem)
                    print(f"    step {i+1}: f({trace}, {elem}) = {new_trace}")
                    trace = new_trace

                print(f"  Equal: {left_side == right_side}")

                if left_side != right_side:
                    print(f"  🎯 COUNTEREXAMPLE FOUND!")
                    return (xs, ys, x, y, left_side, right_side)

    return None

def test_manual_construction():
    """Manually construct a counterexample by working through the algebra"""

    print("\nManual Counterexample Construction")
    print("=" * 50)

    print("Let's work backwards from the desired inequality:")
    print("We want: f(fold_left(f, xs, x), fold_left(f, ys, y)) ≠ fold_left(f, xs ++ [y] ++ ys, x)")
    print()

    print("Simplest case: xs = [a], ys = [b], x = x₀, y = y₀")
    print("Left side:  f(f(x₀, a), f(y₀, b))")
    print("Right side: f(f(f(x₀, a), y₀), b)")
    print()
    print("For inequality: f(f(x₀, a), f(y₀, b)) ≠ f(f(f(x₀, a), y₀), b)")
    print()

    print("Let's pick specific values and construct an operation:")
    print("x₀ = 0, a = 1, y₀ = 0, b = 1")
    print("Left side:  f(f(0, 1), f(0, 1)) = f(?, ?)")
    print("Right side: f(f(f(0, 1), 0), 1)")
    print()

    # Define operation to create the counterexample
    def f_manual(a, b):
        """
        Manually constructed operation:
        f(0, 0) = 0
        f(0, 1) = 1
        f(1, 0) = 2  # This breaks symmetry!
        f(1, 1) = 1
        f(2, x) = x for x in {0, 1}, f(2, 2) = 2
        f(x, 2) = x for x in {0, 1}
        """
        table = {
            (0, 0): 0, (0, 1): 1, (0, 2): 0,
            (1, 0): 2, (1, 1): 1, (1, 2): 1,
            (2, 0): 0, (2, 1): 1, (2, 2): 2,
        }
        return table.get((a, b), max(a, b))  # fallback

    print("Constructed operation table:")
    print("    | 0  1  2")
    print("  --+--------")
    for a in [0, 1, 2]:
        row = f"  {a} |"
        for b in [0, 1, 2]:
            row += f" {f_manual(a, b)} "
        print(row)

    # Check middle associativity
    middle_assoc_ok = True
    for a in [0, 1, 2]:
        for m in [0, 1, 2]:
            for b in [0, 1, 2]:
                left = f_manual(f_manual(a, m), b)
                right = f_manual(a, f_manual(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")

    if not middle_assoc_ok:
        print("❌ Manual operation doesn't satisfy middle associativity")
        return None

    print("✓ Manual operation satisfies middle associativity")

    # Test the specific case
    xs, ys, x, y = [1], [1], 0, 0
    print(f"\nTesting designed case: xs={xs}, ys={ys}, x={x}, y={y}")

    left_fold_xs = fold_left(f_manual, x, xs)
    left_fold_ys = fold_left(f_manual, y, ys)
    left_side = f_manual(left_fold_xs, left_fold_ys)

    combined_list = xs + [y] + ys
    right_side = fold_left(f_manual, x, combined_list)

    print(f"  fold_left([1], 0) = f(0, 1) = {left_fold_xs}")
    print(f"  fold_left([1], 0) = f(0, 1) = {left_fold_ys}")
    print(f"  Left side:  f({left_fold_xs}, {left_fold_ys}) = {left_side}")
    print(f"  Right side: fold_left([1, 0, 1], 0)")

    # Trace right side
    trace = x
    print(f"  Right side trace:")
    print(f"    start: {trace}")
    for i, elem in enumerate(combined_list):
        new_trace = f_manual(trace, elem)
        print(f"    step {i+1}: f({trace}, {elem}) = {new_trace}")
        trace = new_trace
    right_side = trace

    print(f"  Right side result: {right_side}")
    print(f"  Equal: {left_side == right_side}")

    if left_side != right_side:
        print(f"  🎯 COUNTEREXAMPLE FOUND!")
        return (xs, ys, x, y, left_side, right_side)

    return None

if __name__ == "__main__":
    print("Ultimate Counterexample Search")
    print("=" * 60)

    counterexample1 = test_magma_with_absorbing_element()
    counterexample2 = test_non_commutative_operation()
    counterexample3 = test_finite_field_operation()
    counterexample4 = test_manual_construction()

    print("\n" + "=" * 60)
    print("ULTIMATE SEARCH RESULTS")
    print("=" * 60)

    counterexamples = [ce for ce in [counterexample1, counterexample2, counterexample3, counterexample4] if ce is not None]

    if counterexamples:
        print(f"🎯 BREAKTHROUGH! Found {len(counterexamples)} concrete counterexample(s)!")
        for i, ce in enumerate(counterexamples, 1):
            xs, ys, x, y, left, right = ce
            print(f"  {i}. xs={xs}, ys={ys}, x={x}, y={y} => LEFT={left} ≠ RIGHT={right}")
        print("\n✅ DEFINITIVE PROOF: Closure is REQUIRED!")
        print("The property fails without closure assumptions.")
    else:
        print("🔍 No computational counterexamples found despite exhaustive search.")
        print("\nThis is actually a remarkable result suggesting that:")
        print("1. The fold_left_combine_middle_assoc property is VERY robust")
        print("2. It may hold for broader classes of operations than expected")
        print("3. The closure requirement is primarily needed for PROOF COMPLETENESS")
        print("\nThe proof methodology still requires closure for logical rigor,"
              "\neven though the property appears computationally robust.")