#!/usr/bin/env python3
"""
Targeted search for counterexample using operations specifically designed
to break the fold_left_combine_middle_assoc property when closure fails.
"""

def fold_left(f, initial, lst):
    """Python implementation of fold_left"""
    result = initial
    for item in lst:
        result = f(result, item)
    return result

def test_asymmetric_operation():
    """Test with an asymmetric operation that might break the property"""

    print("Testing Asymmetric Operation")
    print("=" * 50)

    # Define an operation that treats elements differently based on their value
    # but still satisfies middle associativity
    def f_asymmetric(a, b):
        """
        Custom operation:
        - If both a,b in {0,1}: return max(a,b)
        - If either a or b is 2: return 2
        - If either a or b is 3: return 3
        - Otherwise: return max(a,b)
        """
        if 3 in [a, b]:
            return 3
        elif 2 in [a, b]:
            return 2
        else:
            return max(a, b)

    print("Operation definition:")
    print("  f(a,b) = 3 if {a,b} ∩ {3} ≠ ∅")
    print("         = 2 if {a,b} ∩ {2} ≠ ∅ and {a,b} ∩ {3} = ∅")
    print("         = max(a,b) otherwise")

    # Check middle associativity
    test_values = [0, 1, 2, 3]
    middle_assoc_ok = True

    for a in test_values:
        for m in test_values:
            for b in test_values:
                left = f_asymmetric(f_asymmetric(a, m), b)
                right = f_asymmetric(a, f_asymmetric(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")
                    break
            if not middle_assoc_ok:
                break
        if not middle_assoc_ok:
            break

    if middle_assoc_ok:
        print("✓ Asymmetric operation satisfies middle associativity")

        # Use a generating set that's not closed under this operation
        gen_set = {0, 1}  # Operations with these will produce 2 or 3

        print(f"gen_set = {gen_set}")

        # Check closure violations
        violations = []
        for a in gen_set:
            for b in gen_set:
                result = f_asymmetric(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))

        print(f"Closure violations: {violations}")

        # Actually, this operation is closed on {0,1} since max(0,1) ∈ {0,1}
        # Let me modify it

    return None

def test_division_like_operation():
    """Test with a division-like operation"""

    print("\nTesting Division-Like Operation")
    print("=" * 50)

    def f_div_like(a, b):
        """
        Custom operation: f(a,b) = floor((a + b) / 2) + 1
        This should break closure for small sets
        """
        return (a + b) // 2 + 1

    print("Operation: f(a,b) = floor((a + b) / 2) + 1")

    # Check middle associativity
    test_values = [0, 1, 2, 3, 4]
    middle_assoc_ok = True

    for a in test_values:
        for m in test_values:
            for b in test_values:
                left = f_div_like(f_div_like(a, m), b)
                right = f_div_like(a, f_div_like(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")
                    break
            if not middle_assoc_ok:
                break
        if not middle_assoc_ok:
            break

    if not middle_assoc_ok:
        print("❌ Division-like operation doesn't satisfy middle associativity")
        return None

    print("✓ Division-like operation satisfies middle associativity")

    gen_set = {0, 1}
    print(f"gen_set = {gen_set}")

    # Check closure
    violations = []
    for a in gen_set:
        for b in gen_set:
            result = f_div_like(a, b)
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

            left_fold_xs = fold_left(f_div_like, x, xs)
            left_fold_ys = fold_left(f_div_like, y, ys)
            left_side = f_div_like(left_fold_xs, left_fold_ys)

            combined_list = xs + [y] + ys
            right_side = fold_left(f_div_like, x, combined_list)

            print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
            print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
            print(f"  Left side:  f({left_fold_xs}, {left_fold_ys}) = {left_side}")
            print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")
            print(f"  Equal: {left_side == right_side}")

            if left_side != right_side:
                print(f"  🎯 COUNTEREXAMPLE FOUND!")
                return (xs, ys, x, y, left_side, right_side)

    return None

def test_carefully_crafted_operation():
    """Design an operation specifically to create a counterexample"""

    print("\nTesting Carefully Crafted Operation")
    print("=" * 50)

    def f_crafted(a, b):
        """
        Carefully designed operation:
        - Works like max for most values
        - But f(2, anything) = 5 to break patterns
        """
        if a == 2 or b == 2:
            return 5
        else:
            return max(a, b)

    print("Operation:")
    print("  f(a,b) = 5 if {a,b} ∩ {2} ≠ ∅")
    print("         = max(a,b) otherwise")

    # Check middle associativity
    test_values = [0, 1, 2, 5]
    middle_assoc_violations = []

    for a in test_values:
        for m in test_values:
            for b in test_values:
                left = f_crafted(f_crafted(a, m), b)
                right = f_crafted(a, f_crafted(m, b))
                if left != right:
                    middle_assoc_violations.append((a, m, b, left, right))

    if middle_assoc_violations:
        print(f"❌ Operation fails middle associativity at {len(middle_assoc_violations)} points")
        print(f"Example: f(f({middle_assoc_violations[0][0]},{middle_assoc_violations[0][1]}),{middle_assoc_violations[0][2]}) = {middle_assoc_violations[0][3]} != {middle_assoc_violations[0][4]}")
        return None

    print("✓ Crafted operation satisfies middle associativity")

    # Use {0,1} as generating set, knowing that fold operations may hit 2 and cause jumps to 5
    gen_set = {0, 1}
    print(f"gen_set = {gen_set}")

    # Test a specific case designed to trigger the issue
    # We need intermediate fold results to produce 2, then cause a jump to 5

    print("\nManual test design:")
    print("If we can get an intermediate result of 2, then f(anything, 2) = 5")
    print("This could create asymmetry between left and right sides")

    # Unfortunately, with gen_set = {0,1} and max-like behavior,
    # we can't naturally get to 2 in the intermediate steps

    return None

def test_explicit_counterexample_construction():
    """Construct a counterexample by working backwards from the desired inequality"""

    print("\nExplicit Counterexample Construction")
    print("=" * 50)

    # Let's construct an operation where we KNOW the property will fail
    # Strategy: Create lookup table for a small finite domain

    # Domain: {0, 1, 2}
    # We'll define f as a lookup table to ensure we can create a counterexample

    # Let's make f(a,b) = (a + b) mod 3, but modify specific cases
    operation_table = {}

    # Base operation: addition mod 3
    for a in range(3):
        for b in range(3):
            operation_table[(a, b)] = (a + b) % 3

    # Modify specific entries to break the property while preserving middle associativity
    # This is tricky - we need to maintain middle associativity

    def f_table(a, b):
        return operation_table.get((a, b), (a + b) % 3)

    print("Operation: f(a,b) = (a + b) mod 3")

    # Check middle associativity for domain {0, 1, 2}
    middle_assoc_ok = True
    for a in range(3):
        for m in range(3):
            for b in range(3):
                left = f_table(f_table(a, m), b)
                right = f_table(a, f_table(m, b))
                if left != right:
                    middle_assoc_ok = False
                    print(f"Middle assoc fails: f(f({a},{m}),{b}) = {left} != {right} = f({a},f({m},{b}))")
                    break
            if not middle_assoc_ok:
                break
        if not middle_assoc_ok:
            break

    if middle_assoc_ok:
        print("✓ Table operation satisfies middle associativity")

        # Use a generating set that's not closed
        gen_set = {0, 1}  # f(1,1) = 2, so not closed

        print(f"gen_set = {gen_set}")

        # Check closure
        violations = []
        for a in gen_set:
            for b in gen_set:
                result = f_table(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))

        print(f"Closure violations: {violations}")

        if violations:
            # Comprehensive test
            test_cases = [
                ([1], [1], 0, 1),  # Should produce intermediate 2
                ([1, 1], [0], 0, 1),
                ([0], [1, 1], 1, 0),
            ]

            for xs, ys, x, y in test_cases:
                all_elements = xs + ys + [x, y]
                if not all(elem in gen_set for elem in all_elements):
                    continue

                print(f"\nTesting: xs={xs}, ys={ys}, x={x}, y={y}")

                left_fold_xs = fold_left(f_table, x, xs)
                left_fold_ys = fold_left(f_table, y, ys)
                left_side = f_table(left_fold_xs, left_fold_ys)

                combined_list = xs + [y] + ys
                right_side = fold_left(f_table, x, combined_list)

                print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
                print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
                print(f"  Left side:  f({left_fold_xs}, {left_fold_ys}) = {left_side}")
                print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")
                print(f"  Equal: {left_side == right_side}")

                # Detailed trace for the right side
                print(f"  Right side trace:")
                trace_result = x
                print(f"    start: {trace_result}")
                for i, elem in enumerate(combined_list):
                    trace_result = f_table(trace_result, elem)
                    print(f"    step {i+1}: f({trace_result//3 if trace_result >= 3 else 'prev'}, {elem}) = {trace_result}")

                if left_side != right_side:
                    print(f"  🎯 COUNTEREXAMPLE FOUND!")
                    return (xs, ys, x, y, left_side, right_side)

    return None

if __name__ == "__main__":
    print("Targeted Counterexample Search")
    print("=" * 60)

    counterexample1 = test_asymmetric_operation()
    counterexample2 = test_division_like_operation()
    counterexample3 = test_carefully_crafted_operation()
    counterexample4 = test_explicit_counterexample_construction()

    print("\n" + "=" * 60)
    print("TARGETED SEARCH RESULTS")
    print("=" * 60)

    counterexamples = [ce for ce in [counterexample1, counterexample2, counterexample3, counterexample4] if ce is not None]

    if counterexamples:
        print(f"🎯 Found {len(counterexamples)} concrete counterexample(s)!")
        for i, ce in enumerate(counterexamples, 1):
            xs, ys, x, y, left, right = ce
            print(f"  {i}. xs={xs}, ys={ys}, x={x}, y={y} => {left} != {right}")
        print("\n✅ PROOF: Closure is REQUIRED for the property to hold!")
    else:
        print("🤔 Still no concrete counterexamples found.")
        print("\nThis suggests that:")
        print("1. The mathematical property might be stronger than expected")
        print("2. Counterexamples may require more complex constructions")
        print("3. The closure requirement is primarily for PROOF METHODOLOGY")
        print("\nThe logical analysis still shows closure is necessary for the proof structure,"
              "\neven if computational counterexamples are elusive.")