#!/usr/bin/env python3

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

# Test the empty list case specifically
xs = []
init_u, init_v = 0, 0

# Left side for empty list
def complex_f(uv, x):
    u, v = uv
    return (max(u, nonNegPlus(v, x)), nonNegPlus(v, x))

left_side = fold_left(complex_f, xs, (init_u, init_v))

# Right side for empty list
scan_results = scan_left(lambda acc, x: nonNegPlus(acc, x), xs, init_v)
max_part = fold_left(max, scan_results, init_u)
plus_part = fold_left(lambda acc, x: nonNegPlus(acc, x), xs, init_v)

right_side = (max_part, plus_part)

print(f"Empty list test:")
print(f"  xs = {xs}")
print(f"  init_u = {init_u}, init_v = {init_v}")
print(f"  Left side: {left_side}")
print(f"  scan_left results: {scan_results}")
print(f"  max_part = fold_left(max, {scan_results}, {init_u}) = {max_part}")
print(f"  plus_part = fold_left(nonNegPlus, {xs}, {init_v}) = {plus_part}")
print(f"  Right side: {right_side}")
print(f"  Equal? {left_side == right_side}")

# Test with different initial values
print("\nTesting with different initial values:")
for init_u, init_v in [(0, 0), (5, 3), (2, 7), (-1, 4)]:
    left_side = fold_left(complex_f, [], (init_u, init_v))
    scan_results = scan_left(lambda acc, x: nonNegPlus(acc, x), [], init_v)
    max_part = fold_left(max, scan_results, init_u)
    plus_part = fold_left(lambda acc, x: nonNegPlus(acc, x), [], init_v)
    right_side = (max_part, plus_part)

    print(f"  init_u={init_u}, init_v={init_v}: left={left_side}, right={right_side}, equal={left_side == right_side}")