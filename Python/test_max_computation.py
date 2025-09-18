#!/usr/bin/env python3
"""
Test the computation of Z_val x ∨_inf Z_val w to understand the Coq goal.
"""

# Z_plus_neg_inf type simulation
class NegInf:
    def __repr__(self):
        return "NegInf"
    def __eq__(self, other):
        return isinstance(other, NegInf)

class ZVal:
    def __init__(self, val: int):
        self.val = val
    def __repr__(self):
        return f"Z_val({self.val})"
    def __eq__(self, other):
        return isinstance(other, ZVal) and self.val == other.val

def z_plus_neg_inf_max(x, y):
    """Z_plus_neg_inf_max operation"""
    print(f"Computing {x} ∨_inf {y}")

    if isinstance(x, NegInf):
        result = y
        print(f"  x is NegInf -> result = {result}")
        return result

    if isinstance(y, NegInf):
        result = x
        print(f"  y is NegInf -> result = {result}")
        return result

    # Both are ZVal
    max_val = max(x.val, y.val)
    result = ZVal(max_val)
    print(f"  Both Z_val -> max({x.val}, {y.val}) = {max_val} -> result = {result}")
    return result

def test_specific_case():
    """Test the specific case from the proof"""
    print("Testing: Z_val x ∨_inf Z_val w")
    print("="*40)

    test_cases = [
        (3, 2),  # x >= w
        (2, 5),  # w > x
        (4, 4),  # x = w
        (-1, -5), # negative numbers
        (0, 0),   # zeros
    ]

    for x_val, w_val in test_cases:
        print(f"\nCase: x = {x_val}, w = {w_val}")
        x = ZVal(x_val)
        w = ZVal(w_val)

        result = z_plus_neg_inf_max(x, w)

        print(f"Expected: Z_val(max({x_val}, {w_val})) = Z_val({max(x_val, w_val)})")
        print(f"Actual:   {result}")
        print(f"Match:    {result == ZVal(max(x_val, w_val))}")

        # Show which case applies
        if x_val >= w_val:
            print(f"Since x >= w: Z.max {x_val} {w_val} = {x_val}")
            print(f"Result should be Z_val({x_val})")
            print(f"Correct: {result == ZVal(x_val)}")
        else:
            print(f"Since w > x: Z.max {x_val} {w_val} = {w_val}")
            print(f"Result should be Z_val({w_val})")
            print(f"Correct: {result == ZVal(w_val)}")

if __name__ == "__main__":
    test_specific_case()

    print("\n" + "="*50)
    print("Key insight for Coq proof:")
    print("Z_val x ∨_inf Z_val w = Z_val (Z.max x w)")
    print("The goal should contain 'In (Z.max x w) (x :: y :: xs'')'")
    print("Not 'In (Z_val (Z.max x w)) ...'")