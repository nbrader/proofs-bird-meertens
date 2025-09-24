#!/usr/bin/env python3

def nonNegPlus(v, x):
    """Coq's nonNegPlus operation: max(0, v + x)"""
    return max(0, v + x)

def fold_left(f, xs, init):
    """Standard fold_left"""
    acc = init
    for x in xs:
        acc = f(acc, x)
    return acc

def inits_rec(xs):
    """inits_rec function that produces all prefixes"""
    result = [[]]  # Always starts with empty list
    for i in range(1, len(xs) + 1):
        result.append(xs[:i])
    return result

def scan_left_v1(f, xs, init):
    """Version 1: includes init and final"""
    result = [init]
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def scan_left_v3(f, xs, init):
    """Version 3: excludes init, includes final"""
    if not xs:
        return []
    result = []
    acc = init
    for x in xs:
        acc = f(acc, x)
        result.append(acc)
    return result

def test_scan_left_inits_relationship():
    """Test the relationship: scan_left f xs i = map (fold_left f prefix i) (inits_rec xs)"""

    test_cases = [
        ([1, 2], "Two positives"),
        ([1, 2, 3], "Three positives"),
        ([], "Empty list"),
    ]

    print("Testing scan_left = map (fold_left f) (inits_rec xs):")
    print("=" * 60)

    for xs, desc in test_cases:
        print(f"{desc}: xs = {xs}")

        # What inits_rec produces
        prefixes = inits_rec(xs)
        print(f"  inits_rec(xs) = {prefixes}")

        # What map (fold_left f prefix i) (inits_rec xs) produces
        prefix_results = [fold_left(nonNegPlus, prefix, 0) for prefix in prefixes]
        print(f"  map (fold_left nonNegPlus prefix 0) (inits_rec xs) = {prefix_results}")

        # Test scan_left versions
        scan_v1 = scan_left_v1(nonNegPlus, xs, 0)
        scan_v3 = scan_left_v3(nonNegPlus, xs, 0)

        print(f"  scan_left_v1 (includes init+final) = {scan_v1}")
        print(f"  scan_left_v3 (excludes init, includes final) = {scan_v3}")

        # Check which version matches the map result
        print(f"  v1 matches map result: {scan_v1 == prefix_results}")
        print(f"  v3 matches map result: {scan_v3 == prefix_results}")
        print()

if __name__ == "__main__":
    test_scan_left_inits_relationship()