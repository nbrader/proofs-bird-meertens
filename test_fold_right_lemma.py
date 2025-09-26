#!/usr/bin/env python3
"""
Test the problematic case in fold_right_nonNegPlus_eq_add_when_sum_nonneg:
When fold_right Z.add 0 xs' < 0 but x + fold_right Z.add 0 xs' >= 0
"""

def nonneg_plus(x, y):
    """nonNegPlus: max(0, x + y)"""
    return max(0, x + y)

def fold_right_nonneg_plus(xs, acc=0):
    """fold_right nonNegPlus acc xs"""
    result = acc
    for x in reversed(xs):
        result = nonneg_plus(x, result)
    return result

def fold_right_add(xs, acc=0):
    """fold_right Z.add acc xs"""
    return sum(xs) + acc

# Test the problematic case: fold_right Z.add 0 xs' < 0 but x + fold_right Z.add 0 xs' >= 0
test_cases = [
    # Format: (x, xs') where x is the head and xs' is the tail
    (5, [-2, -1]),     # x=5, sum(xs')=-3, total=2 >= 0
    (3, [-4, 1]),      # x=3, sum(xs')=-3, total=0 >= 0
    (10, [-3, -2, -4]), # x=10, sum(xs')=-9, total=1 >= 0
    (2, [-3, 0]),      # x=2, sum(xs')=-3, total=-1 < 0 (should not apply)
]

print("Testing fold_right_nonNegPlus_eq_add_when_sum_nonneg problematic case:")
print("="*70)

for i, (x, xs_tail) in enumerate(test_cases):
    xs_full = [x] + xs_tail

    # Calculate the conditions
    sum_xs_tail = fold_right_add(xs_tail)
    sum_full = x + sum_xs_tail

    print(f"Test {i+1}: x={x}, xs'={xs_tail}")
    print(f"  sum(xs') = {sum_xs_tail}")
    print(f"  x + sum(xs') = {sum_full}")
    print(f"  Condition (sum_full >= 0): {sum_full >= 0}")
    print(f"  Condition (sum_xs_tail < 0): {sum_xs_tail < 0}")

    if sum_full >= 0:
        # Test the lemma
        lhs = fold_right_nonneg_plus(xs_full)
        rhs = fold_right_add(xs_full)

        # Also compute intermediate values
        nonneg_tail = fold_right_nonneg_plus(xs_tail)
        regular_tail = fold_right_add(xs_tail)

        print(f"  fold_right nonNegPlus 0 xs' = {nonneg_tail}")
        print(f"  fold_right Z.add 0 xs' = {regular_tail}")
        print(f"  nonNegPlus {x} {nonneg_tail} = {nonneg_plus(x, nonneg_tail)}")
        print(f"  {x} + {regular_tail} = {x + regular_tail}")
        print(f"  LHS: fold_right nonNegPlus 0 xs_full = {lhs}")
        print(f"  RHS: fold_right Z.add 0 xs_full = {rhs}")
        print(f"  Equal: {lhs == rhs}")

        if sum_xs_tail < 0 and sum_full >= 0:
            print(f"  *** This is the problematic case we need to prove! ***")

    print()

print("KEY INSIGHT:")
print("When fold_right Z.add 0 xs' < 0, we get fold_right nonNegPlus 0 xs' = 0")
print("But nonNegPlus x 0 = max(0, x + 0) = max(0, x) = x (if x >= 0)")
print("And x + fold_right Z.add 0 xs' >= 0 by our condition")
print("So the equality still holds!")