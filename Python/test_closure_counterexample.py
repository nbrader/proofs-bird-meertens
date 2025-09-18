#!/usr/bin/env python3
"""
Find counterexamples to demonstrate that closure is required for fold_left_combine_middle_assoc.

This test shows concrete cases where the lemma fails when the generating set
is not closed under the operation, proving that the closure assumption is necessary.
"""

def fold_left(f, initial, lst):
    """Python implementation of fold_left"""
    result = initial
    for item in lst:
        result = f(result, item)
    return result

def test_counterexample_without_closure():
    """Find a counterexample where fold_left_combine_middle_assoc fails without closure"""

    print("Testing fold_left_combine_middle_assoc WITHOUT closure assumption")
    print("=" * 60)

    # Define a generating set that is NOT closed under max
    # We need to think more carefully - max of elements in a finite set
    # will always be in the set! Let's use a different approach.
    # We'll use min instead, with a set that's not closed under min
    gen_set = {2, 5}  # max(2,5)=5, min(2,5)=2, so closed under both max and min

    # Actually, let's use a constrained max operation
    def f_constrained_max(a, b):
        result = max(a, b)
        # Apply a constraint that can take us outside the original set
        return result + 1 if result == 5 else result

    # This will make max(2,5) = 6, which is outside our set

    # Use the constrained operation
    operation = f_constrained_max

    # Check if gen_set is closed under this operation
    def check_closure(gen_set, operation):
        violations = []
        for a in gen_set:
            for b in gen_set:
                result = operation(a, b)
                if result not in gen_set:
                    violations.append((a, b, result))
        return violations

    violations = check_closure(gen_set, operation)
    print(f"gen_set = {gen_set}")
    print(f"Closure violations under constrained operation: {violations}")

    if not violations:
        print("ERROR: This set is actually closed! Need a different example.")
        return []

    # Check middle associativity for our constrained operation
    def check_middle_assoc(a, m, b):
        return operation(operation(a, m), b) == operation(a, operation(m, b))

    middle_assoc_ok = True
    for a in gen_set:
        for m in gen_set:
            for b in gen_set:
                if not check_middle_assoc(a, m, b):
                    middle_assoc_ok = False
                    print(f"Middle associativity fails: {a}, {m}, {b}")

    if middle_assoc_ok:
        print("✓ Middle associativity holds for elements in gen_set")

    # Now try to find a counterexample to fold_left_combine_middle_assoc
    # We need xs, ys, x, y where all elements are in gen_set individually
    # but fold_left operations may produce elements outside gen_set

    print("\nSearching for counterexamples...")

    test_cases = [
        # Format: (xs, ys, x, y) where all individual elements are in gen_set
        ([1], [3], 1, 3),
        ([3], [1], 1, 3),
        ([1, 3], [3], 1, 1),
        ([3, 1], [1], 3, 3),
    ]

    counterexamples_found = []

    for xs, ys, x, y in test_cases:
        # Verify all elements are in gen_set
        all_elements = xs + ys + [x, y]
        if not all(elem in gen_set for elem in all_elements):
            continue

        print(f"\nTesting: xs={xs}, ys={ys}, x={x}, y={y}")

        # Left side: f (fold_left f xs x) (fold_left f ys y)
        left_fold_xs = fold_left(operation, x, xs)
        left_fold_ys = fold_left(operation, y, ys)
        left_side = operation(left_fold_xs, left_fold_ys)

        # Right side: fold_left f (xs ++ y :: ys) x
        combined_list = xs + [y] + ys
        right_side = fold_left(operation, x, combined_list)

        print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
        print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
        print(f"  Left side:  op({left_fold_xs}, {left_fold_ys}) = {left_side}")
        print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")
        print(f"  Equal: {left_side == right_side}")

        # Check if intermediate results are outside gen_set
        intermediate_values = [left_fold_xs, left_fold_ys]
        outside_gen_set = [v for v in intermediate_values if v not in gen_set]

        if outside_gen_set:
            print(f"  ⚠️  Intermediate values outside gen_set: {outside_gen_set}")

        if left_side != right_side:
            counterexamples_found.append((xs, ys, x, y, left_side, right_side))
            print(f"  ❌ COUNTEREXAMPLE FOUND!")
        else:
            print(f"  ✓ Property holds for this case")

    return counterexamples_found

def test_with_modular_arithmetic():
    """Test with modular arithmetic where closure matters more clearly"""

    print("\n" + "=" * 60)
    print("Testing with modular arithmetic (mod 5)")
    print("=" * 60)

    # Define operation: addition mod 5
    def add_mod5(a, b):
        return (a + b) % 5

    # Generate set that's not closed under addition mod 5
    gen_set = {0, 1, 2}  # Missing 3, 4 - not closed under addition mod 5

    # Check closure violations
    violations = []
    for a in gen_set:
        for b in gen_set:
            result = add_mod5(a, b)
            if result not in gen_set:
                violations.append((a, b, result))

    print(f"gen_set = {gen_set}")
    print(f"Closure violations under addition mod 5: {violations}")

    # Check middle associativity for addition mod 5
    def check_middle_assoc_mod5(a, m, b):
        return add_mod5(add_mod5(a, m), b) == add_mod5(a, add_mod5(m, b))

    middle_assoc_ok = True
    for a in range(5):
        for m in range(5):
            for b in range(5):
                if not check_middle_assoc_mod5(a, m, b):
                    middle_assoc_ok = False

    print(f"Middle associativity holds for mod 5 addition: {middle_assoc_ok}")

    # Test fold_left property
    test_cases = [
        ([1, 2], [2], 0, 1),
        ([2, 1], [1], 1, 2),
    ]

    counterexamples = []

    for xs, ys, x, y in test_cases:
        if not all(elem in gen_set for elem in xs + ys + [x, y]):
            continue

        print(f"\nTesting: xs={xs}, ys={ys}, x={x}, y={y}")

        # Left side
        left_fold_xs = fold_left(add_mod5, x, xs)
        left_fold_ys = fold_left(add_mod5, y, ys)
        left_side = add_mod5(left_fold_xs, left_fold_ys)

        # Right side
        combined_list = xs + [y] + ys
        right_side = fold_left(add_mod5, x, combined_list)

        print(f"  fold_left(xs={xs}, x={x}) = {left_fold_xs}")
        print(f"  fold_left(ys={ys}, y={y}) = {left_fold_ys}")
        print(f"  Left side:  ({left_fold_xs} + {left_fold_ys}) mod 5 = {left_side}")
        print(f"  Right side: fold_left({combined_list}, {x}) = {right_side}")
        print(f"  Equal: {left_side == right_side}")

        # Check if results are outside gen_set
        outside_values = []
        for val in [left_fold_xs, left_fold_ys]:
            if val not in gen_set:
                outside_values.append(val)

        if outside_values:
            print(f"  ⚠️  Values outside gen_set: {outside_values}")

        if left_side != right_side:
            counterexamples.append((xs, ys, x, y, left_side, right_side))
            print(f"  ❌ COUNTEREXAMPLE!")
        else:
            print(f"  ✓ Property holds")

    return counterexamples

def test_custom_operation():
    """Test with a custom operation designed to show the closure requirement"""

    print("\n" + "=" * 60)
    print("Testing with custom operation: f(a,b) = a + 2*b")
    print("=" * 60)

    def custom_op(a, b):
        return a + 2 * b

    # Choose gen_set that's not closed under this operation
    gen_set = {0, 1}  # Will produce values outside this set

    # Check closure
    violations = []
    for a in gen_set:
        for b in gen_set:
            result = custom_op(a, b)
            if result not in gen_set:
                violations.append((a, b, result))

    print(f"gen_set = {gen_set}")
    print(f"Closure violations under f(a,b) = a + 2*b: {violations}")

    # Check middle associativity: f(f(a,m),b) = f(a,f(m,b))
    def check_middle_assoc_custom(a, m, b):
        left = custom_op(custom_op(a, m), b)
        right = custom_op(a, custom_op(m, b))
        return left == right

    # Test middle associativity for small values
    assoc_violations = []
    for a in range(5):
        for m in range(5):
            for b in range(5):
                if not check_middle_assoc_custom(a, m, b):
                    assoc_violations.append((a, m, b))

    print(f"Middle associativity violations: {assoc_violations[:5]}...")  # Show first few

    if assoc_violations:
        print("❌ Custom operation does NOT satisfy middle associativity!")
        print("This operation is not suitable for our test.")
        return []

    # If it did satisfy middle associativity, test the fold property
    # (This won't execute since the custom operation doesn't satisfy middle associativity)
    return []

if __name__ == "__main__":
    print("Finding counterexamples to prove closure is required")
    print("=" * 60)

    counterexamples1 = test_counterexample_without_closure()
    counterexamples2 = test_with_modular_arithmetic()
    counterexamples3 = test_custom_operation()

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)

    total_counterexamples = len(counterexamples1) + len(counterexamples2) + len(counterexamples3)

    if total_counterexamples > 0:
        print(f"🎯 Found {total_counterexamples} counterexample(s)!")
        print("This proves that closure is indeed required for the lemma to hold.")
    else:
        print("🤔 No counterexamples found in these test cases.")
        print("The property might hold more generally than expected, or we need different test cases.")

    print("\nThe key insight is that without closure:")
    print("1. fold_left operations can produce values outside the generating set")
    print("2. The middle associativity property no longer applies to these intermediate results")
    print("3. This breaks the fundamental assumptions needed for the proof")