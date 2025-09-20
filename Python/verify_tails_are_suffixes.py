#!/usr/bin/env python3

"""
Verify the tails_are_suffixes conjecture:
forall xs ys, In ys (tails xs) -> exists zs, zs ++ ys = xs
"""

def tails(xs):
    """tails function - returns all suffixes"""
    result = []
    for i in range(len(xs) + 1):
        result.append(xs[i:])
    return result

def test_tails_are_suffixes():
    """Test that every element of tails xs is a suffix of xs"""

    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        [1, 2, 3, 4],
        ['a', 'b', 'c'],
    ]

    all_passed = True

    for xs in test_cases:
        tails_xs = tails(xs)
        print(f"Testing xs={xs}")
        print(f"  tails(xs)={tails_xs}")

        for ys in tails_xs:
            # Check if there exists zs such that zs + ys = xs
            # This means ys is a suffix of xs
            if len(ys) <= len(xs):
                zs = xs[:len(xs) - len(ys)]
                concatenated = zs + ys

                print(f"    ys={ys}, zs={zs}, zs+ys={concatenated}")

                if concatenated == xs:
                    print(f"    ✓ PASS: {zs} + {ys} = {xs}")
                else:
                    print(f"    ✗ FAIL: {zs} + {ys} ≠ {xs}")
                    all_passed = False
            else:
                print(f"    ✗ FAIL: ys={ys} longer than xs={xs}")
                all_passed = False
        print()

    if all_passed:
        print("All tests passed! The conjecture appears to be TRUE.")
    else:
        print("Some tests failed. The conjecture may be FALSE.")

    return all_passed

if __name__ == "__main__":
    test_tails_are_suffixes()