#!/usr/bin/env python3
"""
Test script to verify associativity of nonNegPlus operation.

The nonNegPlus operation is defined as:
nonNegPlus(x, y) = max(0, x + y)

For associativity, we need:
nonNegPlus(nonNegPlus(x, y), z) = nonNegPlus(x, nonNegPlus(y, z))
"""

import random
import itertools
from typing import List, Tuple

def non_neg_plus(x: int, y: int) -> int:
    """
    Coq definition: if Z.leb 0 (x + y) then x + y else 0
    Which is equivalent to: max(0, x + y)
    """
    return max(0, x + y)

def test_associativity(x: int, y: int, z: int) -> bool:
    """Test if nonNegPlus is associative for given x, y, z"""
    left = non_neg_plus(non_neg_plus(x, y), z)
    right = non_neg_plus(x, non_neg_plus(y, z))
    return left == right

def test_associativity_verbose(x: int, y: int, z: int) -> Tuple[bool, int, int]:
    """Test associativity and return detailed results"""
    left = non_neg_plus(non_neg_plus(x, y), z)
    right = non_neg_plus(x, non_neg_plus(y, z))
    return left == right, left, right

def comprehensive_test():
    """Run comprehensive tests for nonNegPlus associativity"""
    print("Testing nonNegPlus associativity...")
    print("nonNegPlus(x, y) = max(0, x + y)")
    print()

    # Test small values systematically
    print("=== Systematic test on small values ===")
    test_range = range(-10, 11)
    failed_cases = []
    total_tests = 0

    for x, y, z in itertools.product(test_range, repeat=3):
        total_tests += 1
        is_assoc, left, right = test_associativity_verbose(x, y, z)
        if not is_assoc:
            failed_cases.append((x, y, z, left, right))
            if len(failed_cases) <= 10:  # Print first 10 failures
                print(f"FAIL: ({x}, {y}, {z}) -> {left} != {right}")

    print(f"Systematic tests: {total_tests - len(failed_cases)}/{total_tests} passed")
    if failed_cases:
        print(f"Failed cases: {len(failed_cases)}")
    else:
        print("All systematic tests PASSED!")
    print()

    # Random testing with larger values
    print("=== Random testing with larger values ===")
    random_failures = 0
    random_tests = 10000

    for _ in range(random_tests):
        x = random.randint(-1000, 1000)
        y = random.randint(-1000, 1000)
        z = random.randint(-1000, 1000)

        if not test_associativity(x, y, z):
            random_failures += 1
            if random_failures <= 5:  # Print first 5 random failures
                is_assoc, left, right = test_associativity_verbose(x, y, z)
                print(f"RANDOM FAIL: ({x}, {y}, {z}) -> {left} != {right}")

    print(f"Random tests: {random_tests - random_failures}/{random_tests} passed")
    if random_failures == 0:
        print("All random tests PASSED!")
    print()

    # Edge cases
    print("=== Edge case testing ===")
    edge_cases = [
        (0, 0, 0),
        (-1, 1, 0),
        (1, -1, 0),
        (-5, 3, 2),
        (10, -20, 5),
        (-100, 50, 50),
        (1000, -500, -400)
    ]

    edge_failures = []
    for x, y, z in edge_cases:
        is_assoc, left, right = test_associativity_verbose(x, y, z)
        if not is_assoc:
            edge_failures.append((x, y, z, left, right))
            print(f"EDGE FAIL: ({x}, {y}, {z}) -> {left} != {right}")
        else:
            print(f"EDGE PASS: ({x}, {y}, {z}) -> {left} = {right}")

    if not edge_failures:
        print("All edge cases PASSED!")
    print()

    # Summary
    total_failures = len(failed_cases) + random_failures + len(edge_failures)
    total_all_tests = total_tests + random_tests + len(edge_cases)

    print("=== SUMMARY ===")
    print(f"Total tests run: {total_all_tests}")
    print(f"Total failures: {total_failures}")

    if total_failures == 0:
        print("🎉 nonNegPlus IS ASSOCIATIVE!")
        print("This confirms we can prove nonNegPlus_assoc in Coq.")
    else:
        print("❌ nonNegPlus is NOT associative")
        print("Cannot prove nonNegPlus_assoc in Coq - it's false!")

    return total_failures == 0

def demonstrate_operation():
    """Demonstrate how nonNegPlus works with examples"""
    print("=== nonNegPlus operation examples ===")
    examples = [
        (3, 4),    # positive + positive
        (-2, 5),   # negative + positive (result positive)
        (-3, 2),   # negative + positive (result negative, so 0)
        (-5, -3),  # negative + negative
        (0, 7),    # zero + positive
        (0, -2),   # zero + negative
        (0, 0)     # zero + zero
    ]

    for x, y in examples:
        result = non_neg_plus(x, y)
        print(f"nonNegPlus({x:3}, {y:3}) = max(0, {x:3} + {y:3}) = max(0, {x+y:3}) = {result:3}")
    print()

if __name__ == "__main__":
    demonstrate_operation()
    is_associative = comprehensive_test()

    if is_associative:
        print("\n✅ Ready to prove nonNegPlus_assoc in Coq!")
    else:
        print("\n❌ Cannot prove nonNegPlus_assoc - the property is false!")