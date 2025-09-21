#!/usr/bin/env python3

"""
Test the specific pattern of inits_tails_duality to understand the computational relationship.
This will help guide the Coq proof strategy.
"""

def fold_right(f, init, lst):
    """fold_right f init lst"""
    acc = init
    for x in reversed(lst):
        acc = f(x, acc)
    return acc

def cons(x, xs):
    """cons operation"""
    return [x] + xs

def inits_pattern(x, prev_result):
    """The function used in inits: fun x => cons [] ∘ map (cons x)"""
    def map_cons_x(lst):
        return [[x] + sublist for sublist in lst]
    return [[]] + map_cons_x(prev_result)

def tails_pattern(x, prev_result):
    """The pattern match function used in tails"""
    if prev_result == []:
        return [[]]  # This case should be impossible
    else:
        # prev_result is xs :: xss, return (x::xs) :: (xs::xss)
        xs = prev_result[0]
        xss = prev_result[1:]
        return [[x] + xs] + prev_result

def compute_inits(lst):
    """Compute inits using fold_right"""
    return fold_right(inits_pattern, [[]], lst)

def compute_tails(lst):
    """Compute tails using fold_right"""
    return fold_right(tails_pattern, [[]], lst)

def test_inits_tails_duality():
    """Test the duality relationship"""
    test_cases = [
        [],
        [1],
        [1, 2],
        [1, 2, 3],
        ['a', 'b', 'c']
    ]

    print("Testing inits_tails_duality:")
    print("map rev (inits xs) = rev (tails (rev xs))")
    print()

    all_pass = True

    for i, lst in enumerate(test_cases):
        # LHS: map rev (inits xs)
        inits_result = compute_inits(lst)
        lhs = [list(reversed(prefix)) for prefix in inits_result]

        # RHS: rev (tails (rev xs))
        rev_lst = list(reversed(lst))
        tails_result = compute_tails(rev_lst)
        rhs = list(reversed(tails_result))

        passed = lhs == rhs
        all_pass = all_pass and passed

        print(f"Test {i+1}: {lst}")
        print(f"  inits({lst}) = {inits_result}")
        print(f"  map rev (inits): {lhs}")
        print(f"  rev({lst}) = {rev_lst}")
        print(f"  tails(rev): {tails_result}")
        print(f"  rev(tails(rev)): {rhs}")
        print(f"  Equal: {passed}")
        print()

    print(f"Overall result: {'✅ ALL TESTS PASS' if all_pass else '❌ SOME TESTS FAIL'}")

    if not all_pass:
        print("\nDetailed analysis of first failure:")
        lst = [1, 2]
        inits_result = compute_inits(lst)
        lhs = [list(reversed(prefix)) for prefix in inits_result]
        rev_lst = list(reversed(lst))
        tails_result = compute_tails(rev_lst)
        rhs = list(reversed(tails_result))

        print(f"For {lst}:")
        print(f"  Step-by-step LHS:")
        print(f"    inits({lst}) = {inits_result}")
        print(f"    map rev = {lhs}")
        print(f"  Step-by-step RHS:")
        print(f"    rev({lst}) = {rev_lst}")
        print(f"    tails({rev_lst}) = {tails_result}")
        print(f"    rev(tails) = {rhs}")

if __name__ == "__main__":
    test_inits_tails_duality()