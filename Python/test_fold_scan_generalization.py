#!/usr/bin/env python3

"""
Test different generalizations of fold_scan_fusion_pair_dual to find one that works
"""

def nonNegPlus(x, y):
    """Non-negative addition: max(0, x + y)"""
    return max(0, x + y)

def scan_left(f, xs, init):
    """Left scan: returns list of intermediate results"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def fold_left(f, xs, init):
    """Left fold"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def test_generalization(test_name, invariant_check):
    """Test a specific generalization pattern"""
    print(f"\n=== Testing {test_name} ===")

    test_cases = [
        ([1, 2], 0, 0),
        ([1, -2, 3], 0, 0),
        ([-1, 2], 0, 0),
        ([5], 0, 0),
        ([1, 2], 0, 1),  # Different v_acc
        ([1, 2], 1, 0),  # Different u_acc
        ([1, 2], 2, 1),  # u_acc > v_acc
        ([1, 2], 1, 2),  # u_acc < v_acc
    ]

    all_passed = True

    for xs, u_acc, v_acc in test_cases:
        if not invariant_check(xs, u_acc, v_acc):
            continue  # Skip cases that don't satisfy the invariant

        # Left side: complex fold_left
        def complex_f(uv, x):
            u, v = uv
            return (max(u, nonNegPlus(v, x)), nonNegPlus(v, x))

        left_result = fold_left(complex_f, xs, (u_acc, v_acc))

        # Right side: tuple of fold_left operations
        scan_result = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, v_acc)
        max_part = fold_left(max, scan_result, u_acc)
        plus_part = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, v_acc)
        right_result = (max_part, plus_part)

        equal = left_result == right_result
        print(f"  xs={xs}, u_acc={u_acc}, v_acc={v_acc}: {left_result} vs {right_result} = {equal}")

        if not equal:
            all_passed = False

    return all_passed

# Test 1: Only (0,0) case
def only_zero_zero(xs, u_acc, v_acc):
    return u_acc == 0 and v_acc == 0

# Test 2: v_acc = 0, any u_acc >= 0
def v_zero_u_nonneg(xs, u_acc, v_acc):
    return v_acc == 0 and u_acc >= 0

# Test 3: u_acc >= v_acc >= 0 (the one that failed)
def u_ge_v_nonneg(xs, u_acc, v_acc):
    return v_acc >= 0 and u_acc >= v_acc

# Test 4: Both zero or equal
def both_zero_or_equal(xs, u_acc, v_acc):
    return (u_acc == 0 and v_acc == 0) or (u_acc == v_acc and u_acc >= 0)

# Test 5: Scan starting values align properly
def scan_aligned(xs, u_acc, v_acc):
    # Only cases where u_acc is already the max of the scan prefix
    if v_acc < 0:
        return False
    scan_result = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, v_acc)
    return u_acc == max(scan_result + [0])

# Run tests
test_generalization("Only (0,0)", only_zero_zero)
test_generalization("v_acc=0, u_acc>=0", v_zero_u_nonneg)
test_generalization("u_acc >= v_acc >= 0", u_ge_v_nonneg)
test_generalization("Both zero or equal nonneg", both_zero_or_equal)
test_generalization("Scan-aligned", scan_aligned)