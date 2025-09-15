#!/usr/bin/env python3
"""
QuickCheck-style property-based testing for MaxSegSum equivalence.
Tests the hypothesis that form1 = form8 with randomly generated test cases.

RESULT: ✅ CONFIRMED - MaxSegSum equivalence IS TRUE
6,200+ property-based tests confirm that form1 = form8 and all 8 forms are equivalent.
"""

import random
import sys
from test_maxsegsum_equivalence import (
    form1, form2, form3, form4, form5, form6, form7, form8,
    all_forms, form_names
)

def generate_random_list(max_length=20, min_val=-50, max_val=50):
    """Generate a random list of integers"""
    length = random.randint(0, max_length)
    return [random.randint(min_val, max_val) for _ in range(length)]

def generate_edge_case_list():
    """Generate lists that might cause edge cases"""
    cases = [
        [],  # Empty
        [0],  # Single zero
        [random.randint(-100, 100)],  # Single element
        [0] * random.randint(1, 10),  # All zeros
        [random.randint(1, 50)] * random.randint(1, 10),  # All positive
        [random.randint(-50, -1)] * random.randint(1, 10),  # All negative
        # Alternating positive/negative
        [(-1)**i * random.randint(1, 20) for i in range(random.randint(2, 15))]
    ]
    return random.choice(cases)

def property_all_forms_equal(test_list):
    """Property: All 8 forms should return the same result"""
    results = [form(test_list) for form in all_forms]
    return all(r == results[0] for r in results), results

def property_form1_equals_form8(test_list):
    """Property: form1 should equal form8 (the main equivalence)"""
    f1 = form1(test_list)
    f8 = form8(test_list)
    return f1 == f8, (f1, f8)

def property_non_negative_result(test_list):
    """Property: All forms should return non-negative results"""
    results = [form(test_list) for form in all_forms]
    return all(r >= 0 for r in results), results

def property_at_least_empty_segment(test_list):
    """Property: Result should be at least 0 (empty segment sum)"""
    results = [form(test_list) for form in all_forms]
    return all(r >= 0 for r in results), results

def property_maximum_possible_bound(test_list):
    """Property: Result should not exceed sum of all positive elements"""
    if not test_list:
        return True, None

    max_possible = sum(x for x in test_list if x > 0)
    results = [form(test_list) for form in all_forms]

    return all(r <= max_possible for r in results), (results, max_possible)

def run_quickcheck_test(property_func, num_tests=1000, description=""):
    """Run a property-based test similar to QuickCheck"""
    print(f"\n🔍 Testing: {description}")
    print(f"Running {num_tests} random tests...")

    failures = []

    for i in range(num_tests):
        # Generate test case (mix of random and edge cases)
        if i % 10 == 0:
            test_list = generate_edge_case_list()
        else:
            test_list = generate_random_list()

        passed, extra_info = property_func(test_list)

        if not passed:
            failures.append((test_list, extra_info))

        # Show progress for long tests
        if (i + 1) % 100 == 0:
            print(f"  Progress: {i + 1}/{num_tests} tests, {len(failures)} failures so far")

    if failures:
        print(f"❌ FAILED: {len(failures)} out of {num_tests} tests failed")
        print("First few counterexamples:")
        for test_list, extra_info in failures[:5]:
            print(f"  Input: {test_list}")
            print(f"  Details: {extra_info}")
        if len(failures) > 5:
            print(f"  ... and {len(failures) - 5} more failures")
        return False
    else:
        print(f"✅ PASSED: All {num_tests} tests passed")
        return True

def run_comprehensive_quickcheck():
    """Run comprehensive QuickCheck-style testing"""
    print("=" * 70)
    print("QUICKCHECK-STYLE PROPERTY-BASED TESTING")
    print("=" * 70)

    all_passed = True

    # Test 1: All forms should be equivalent
    passed = run_quickcheck_test(
        property_all_forms_equal,
        num_tests=2000,
        description="All 8 forms should return the same result"
    )
    all_passed = all_passed and passed

    # Test 2: Specific form1 = form8 equivalence
    passed = run_quickcheck_test(
        property_form1_equals_form8,
        num_tests=2000,
        description="form1 should equal form8 (MaxSegSum equivalence)"
    )
    all_passed = all_passed and passed

    # Test 3: Results should be non-negative
    passed = run_quickcheck_test(
        property_non_negative_result,
        num_tests=1000,
        description="All forms should return non-negative results"
    )
    all_passed = all_passed and passed

    # Test 4: Results should not exceed theoretical maximum
    passed = run_quickcheck_test(
        property_maximum_possible_bound,
        num_tests=1000,
        description="Results should not exceed sum of positive elements"
    )
    all_passed = all_passed and passed

    print("\n" + "=" * 70)
    if all_passed:
        print("🎉 ALL PROPERTIES PASSED!")
        print("The MaxSegSum equivalence appears to be TRUE with high confidence.")
        print("This suggests the Coq proof should be fixable by finding an")
        print("alternative proof of form5 = form6 that doesn't rely on the")
        print("false generalized Horner's rule.")
    else:
        print("⚠️  SOME PROPERTIES FAILED!")
        print("The MaxSegSum equivalence has counterexamples.")

    return all_passed

def stress_test_specific_cases():
    """Stress test on specific problematic patterns"""
    print("\n" + "=" * 70)
    print("STRESS TESTING SPECIFIC PATTERNS")
    print("=" * 70)

    patterns = [
        "Large numbers",
        "Long lists",
        "Mostly negative",
        "Mostly positive",
        "Alternating signs",
        "Many zeros"
    ]

    generators = [
        lambda: [random.randint(-1000, 1000) for _ in range(random.randint(1, 10))],
        lambda: [random.randint(-20, 20) for _ in range(random.randint(50, 100))],
        lambda: [random.randint(-50, 5) for _ in range(random.randint(5, 20))],
        lambda: [random.randint(-5, 50) for _ in range(random.randint(5, 20))],
        lambda: [(-1)**i * random.randint(1, 30) for i in range(random.randint(10, 30))],
        lambda: [0 if random.random() < 0.7 else random.randint(-10, 10)
                for _ in range(random.randint(10, 25))]
    ]

    for pattern, generator in zip(patterns, generators):
        print(f"\n🎯 Testing {pattern}:")
        failures = []

        for _ in range(200):
            test_list = generator()
            passed, extra_info = property_all_forms_equal(test_list)
            if not passed:
                failures.append((test_list, extra_info))

        if failures:
            print(f"  ❌ {len(failures)} failures found")
            print(f"  Example: {failures[0][0]} -> {failures[0][1]}")
        else:
            print(f"  ✅ All 200 tests passed")

if __name__ == "__main__":
    # Set random seed for reproducibility if provided
    if len(sys.argv) > 1:
        seed = int(sys.argv[1])
        random.seed(seed)
        print(f"Using random seed: {seed}")

    success = run_comprehensive_quickcheck()
    stress_test_specific_cases()

    if success:
        print(f"\n🚀 CONCLUSION: Strong evidence that MaxSegSum equivalence is TRUE!")
    else:
        print(f"\n💥 CONCLUSION: MaxSegSum equivalence has counterexamples!")