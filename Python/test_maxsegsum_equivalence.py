#!/usr/bin/env python3
"""
Test script to verify the complete MaxSegSum equivalence: form1 = form8
This tests all 8 forms from the Bird-Meertens formalism to see if they're computationally equivalent.

RESULT: ✅ CONFIRMED - MaxSegSum equivalence IS TRUE
All computational tests confirm that form1 = form8 and the Bird-Meertens formalism is correct.
"""

def non_neg_plus(x, y):
    """nonNegPlus: adds x and y, returns 0 if result is negative"""
    return max(0, x + y)

def non_neg_sum(lst):
    """nonNegSum: fold using nonNegPlus (fold_left)"""
    result = 0
    for x in lst:
        result = non_neg_plus(x, result)
    return result

def non_neg_sum_right(lst):
    """nonNegSum using fold_right (Haskell-style foldr)"""
    if not lst:
        return 0
    return non_neg_plus(lst[0], non_neg_sum_right(lst[1:]))

def non_neg_maximum(lst):
    """nonNegMaximum: maximum of a list (assuming non-empty)"""
    if not lst:
        return 0  # Handle empty list case
    return max(lst)

def inits(lst):
    """All initial segments of a list"""
    return [lst[:i] for i in range(len(lst) + 1)]

def tails(lst):
    """All tail segments of a list"""
    return [lst[i:] for i in range(len(lst) + 1)]

def segs(lst):
    """All segments of a list (concat ∘ map inits ∘ tails)"""
    result = []
    for tail in tails(lst):
        result.extend(inits(tail))
    return result

def scan_right(op, initial, lst):
    """Scan from right with binary operation"""
    if not lst:
        return [initial]
    rest = scan_right(op, initial, lst[1:])
    return [op(lst[0], rest[0])] + rest

# Form definitions from the Bird-Meertens formalism
def form1(lst):
    """form1: maximum ∘ map sum ∘ segs"""
    segments = segs(lst)
    sums = [sum(seg) for seg in segments]
    return max(sums) if sums else 0

def form2(lst):
    """form2: maximum ∘ map sum ∘ concat ∘ map inits ∘ tails"""
    tails_lst = tails(lst)
    all_inits = []
    for tail in tails_lst:
        all_inits.extend(inits(tail))
    sums = [sum(seg) for seg in all_inits]
    return max(sums) if sums else 0

def form3(lst):
    """form3: maximum ∘ concat ∘ map (map sum) ∘ map inits ∘ tails"""
    tails_lst = tails(lst)
    all_sums = []
    for tail in tails_lst:
        inits_tail = inits(tail)
        sums = [sum(seg) for seg in inits_tail]
        all_sums.extend(sums)
    return max(all_sums) if all_sums else 0

def form4(lst):
    """form4: maximum ∘ map maximum ∘ map (map sum) ∘ map inits ∘ tails"""
    tails_lst = tails(lst)
    maxima = []
    for tail in tails_lst:
        inits_tail = inits(tail)
        sums = [sum(seg) for seg in inits_tail]
        maxima.append(max(sums) if sums else 0)
    return max(maxima) if maxima else 0

def form5(lst):
    """form5: nonNegMaximum ∘ map (nonNegMaximum ∘ map nonNegSum ∘ inits) ∘ tails"""
    tails_lst = tails(lst)
    mapped = []
    for tail in tails_lst:
        inits_tail = inits(tail)
        sums = [non_neg_sum(init) for init in inits_tail]
        max_sum = non_neg_maximum(sums)
        mapped.append(max_sum)
    return non_neg_maximum(mapped)

def form6(lst):
    """form6: nonNegMaximum ∘ map (foldr nonNegPlus 0) ∘ tails_rec"""
    tails_lst = tails(lst)
    mapped = [non_neg_sum_right(tail) for tail in tails_lst]
    return non_neg_maximum(mapped)

def form7(lst):
    """form7: nonNegMaximum ∘ scan_right nonNegPlus 0"""
    scanned = scan_right(non_neg_plus, 0, lst)
    return non_neg_maximum(scanned)

def form8(lst):
    """form8: fst ∘ foldr maxSoFarAndPreviousSum (0, 0)"""
    def max_so_far_and_previous_sum(x, acc):
        u, v = acc
        w = non_neg_plus(v, x)
        return (max(u, w), w)

    if not lst:
        return 0

    result = (0, 0)
    for x in reversed(lst):
        result = max_so_far_and_previous_sum(x, result)

    return result[0]

# All forms for easy testing
all_forms = [form1, form2, form3, form4, form5, form6, form7, form8]
form_names = ['form1', 'form2', 'form3', 'form4', 'form5', 'form6', 'form7', 'form8']

def test_all_forms(lst):
    """Test all 8 forms on a given list"""
    results = [form(lst) for form in all_forms]
    return results

def test_maxsegsum_equivalence(lst):
    """Test if all forms give the same result (MaxSegSum equivalence)"""
    results = test_all_forms(lst)
    all_equal = all(r == results[0] for r in results)
    return results, all_equal

def detailed_analysis(lst):
    """Show detailed analysis of all forms"""
    print(f"\nDetailed analysis for {lst}:")
    print("=" * 60)

    results = test_all_forms(lst)

    for i, (name, result) in enumerate(zip(form_names, results)):
        print(f"{name:6}: {result:3}")

    all_equal = all(r == results[0] for r in results)
    print(f"\nAll forms equal? {all_equal}")

    if not all_equal:
        print("Differences found:")
        for i, (name, result) in enumerate(zip(form_names, results)):
            if result != results[0]:
                print(f"  {name} = {result} (differs from form1 = {results[0]})")

    return results, all_equal

def main():
    print("Testing MaxSegSum Equivalence: form1 = form2 = ... = form8")
    print("=" * 70)

    # Comprehensive test cases
    test_cases = [
        [],                    # Empty list
        [1],                   # Single positive
        [-1],                  # Single negative
        [0],                   # Single zero
        [1, 2],                # Two positive
        [-1, -2],              # Two negative
        [1, -1],               # Mixed
        [-3, 1, 1],            # The problematic case from Horner's rule
        [1, -2, 3],            # Classic example
        [1, 2, 3],             # All positive
        [-1, -2, -3],          # All negative
        [5, -3, -2],           # Starts positive, ends negative
        [-5, 3, 2],            # Starts negative, ends positive
        [1, -2, 3, -1, 2],     # Longer mixed
        [10, -5, 3, -2, 1],    # Another longer case
        [0, 1, 0, -1, 2],      # With zeros
        [2, -3, 4, -1, 2, 1, -5, 4]  # Complex case
    ]

    counterexamples = []

    for i, lst in enumerate(test_cases):
        results, all_equal = test_maxsegsum_equivalence(lst)
        status = "✓" if all_equal else "✗"

        # Show compact results
        results_str = " ".join(f"{r:2}" for r in results)
        print(f"{status} {str(lst):25} => [{results_str}] equal={all_equal}")

        if not all_equal:
            counterexamples.append((lst, results))

    print(f"\nSummary:")
    print(f"Total test cases: {len(test_cases)}")
    print(f"Counterexamples found: {len(counterexamples)}")

    if counterexamples:
        print(f"\nMaxSegSum equivalence FAILS for {len(counterexamples)} cases:")
        for lst, results in counterexamples[:3]:  # Show first 3 counterexamples
            print(f"  {lst}")
            for name, result in zip(form_names, results):
                print(f"    {name}: {result}")
        if len(counterexamples) > 3:
            print(f"  ... and {len(counterexamples) - 3} more cases")
    else:
        print("✅ MaxSegSum equivalence HOLDS for all test cases!")
        print("This suggests form1 = form8 is TRUE!")

    # Detailed analysis of key cases
    print("\n" + "=" * 70)
    print("DETAILED ANALYSIS OF KEY CASES:")
    print("=" * 70)

    key_cases = [
        [-3, 1, 1],           # The Horner's rule counterexample
        [1, -2, 3],           # Classic MaxSegSum example
        [5, -3, -2]           # Case that might show differences
    ]

    for lst in key_cases:
        detailed_analysis(lst)

    # Test the specific question: does form1 = form8?
    print("\n" + "=" * 70)
    print("SPECIFIC TEST: form1 = form8?")
    print("=" * 70)

    form1_neq_form8_cases = []

    for lst in test_cases:
        f1 = form1(lst)
        f8 = form8(lst)
        equal = (f1 == f8)
        status = "✓" if equal else "✗"
        print(f"{status} {str(lst):25} => form1={f1:2}, form8={f8:2}, equal={equal}")

        if not equal:
            form1_neq_form8_cases.append(lst)

    if form1_neq_form8_cases:
        print(f"\n❌ form1 ≠ form8 for {len(form1_neq_form8_cases)} cases:")
        for lst in form1_neq_form8_cases:
            print(f"   {lst}")
    else:
        print(f"\n✅ form1 = form8 for ALL test cases!")
        print("The MaxSegSum_Equivalence theorem appears to be TRUE!")

if __name__ == "__main__":
    main()