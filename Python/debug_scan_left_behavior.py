#!/usr/bin/env python3

"""
Debug the exact behavior of scan_left to understand the alignment needed
for fold_scan_fusion_pair_dual proof.
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

# Test specific cases to understand scan_left behavior
test_cases = [
    [],
    [1],
    [1, 2],
    [1, -2, 3],
    [-1, -2, -3]
]

print("Understanding scan_left behavior:")
for i, xs in enumerate(test_cases):
    init_v = 0
    scan_result = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, init_v)
    fold_result = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, init_v)

    print(f"\nTest {i+1}: xs = {xs}, init = {init_v}")
    print(f"  scan_left result: {scan_result}")
    print(f"  fold_left result: {fold_result}")
    print(f"  scan_left length: {len(scan_result)}")
    print(f"  scan_left[0] = {scan_result[0]} (should be init)")
    print(f"  scan_left[-1] = {scan_result[-1]} (should equal fold_left)")

    # Now test fold_left Z.max on the scan result
    if scan_result:
        max_of_scan = fold_left(max, scan_result, 0)
        print(f"  fold_left max (scan_result, 0) = {max_of_scan}")

print("\n" + "="*50)
print("Testing the exact conjecture:")

for i, xs in enumerate(test_cases):
    print(f"\nTest {i+1}: xs = {xs}")

    # Left side: complex fold_left
    def complex_f(uv, x):
        u, v = uv
        return (max(u, nonNegPlus(v, x)), nonNegPlus(v, x))

    left_result = fold_left(complex_f, xs, (0, 0))

    # Right side: tuple of two fold_left operations
    scan_result = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, 0)
    max_part = fold_left(max, scan_result, 0)
    plus_part = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, 0)
    right_result = (max_part, plus_part)

    print(f"  Left side: {left_result}")
    print(f"  scan_left: {scan_result}")
    print(f"  max part: {max_part}")
    print(f"  plus part: {plus_part}")
    print(f"  Right side: {right_result}")
    print(f"  Equal? {left_result == right_result}")