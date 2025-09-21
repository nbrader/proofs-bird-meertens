#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def scan_left_v1(f, xs, init):
    """Version 1: scan_left that INCLUDES the initial value at the start"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def scan_left_v2(f, xs, init):
    """Version 2: scan_left that EXCLUDES the final value (removes last element)"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result[:-1]  # Remove the last element

def scan_left_v3(f, xs, init):
    """Version 3: scan_left that produces intermediate results ONLY (no init, no final)"""
    if not xs:
        return []
    result = []
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def nonNegMaximum_dual(xs):
    """nonNegMaximum_dual: fold_left max xs 0"""
    if not xs:
        return 0
    acc = 0
    for x in xs:
        acc = max(acc, x)
    return acc

def test_scan_left_versions():
    """Test different scan_left implementations"""
    test_cases = [
        ([1, 2], "Two positives"),
        ([1, 2, 3], "Three positives"),
        ([-1, -2], "Two negatives"),
        ([], "Empty list"),
    ]

    print("Testing different scan_left implementations:")
    print("=" * 60)

    for xs, desc in test_cases:
        print(f"{desc}: xs = {xs}")

        v1_result = scan_left_v1(nonNegPlus, xs, 0)
        v2_result = scan_left_v2(nonNegPlus, xs, 0)
        v3_result = scan_left_v3(nonNegPlus, xs, 0)

        print(f"  v1 (includes init + final): {v1_result}")
        print(f"  v2 (includes init, excludes final): {v2_result}")
        print(f"  v3 (excludes init, includes final): {v3_result}")

        print(f"  nonNegMaximum_dual(v1): {nonNegMaximum_dual(v1_result)}")
        print(f"  nonNegMaximum_dual(v2): {nonNegMaximum_dual(v2_result)}")
        print(f"  nonNegMaximum_dual(v3): {nonNegMaximum_dual(v3_result)}")
        print()

if __name__ == "__main__":
    test_scan_left_versions()