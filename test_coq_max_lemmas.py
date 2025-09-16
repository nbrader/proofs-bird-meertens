#!/usr/bin/env python3
"""
Search for existing Coq lemmas about fold_right and Z.max.
This helps identify what might already be available in the standard library.
"""

import subprocess
import os

def search_coq_docs():
    """Search for relevant lemmas in Coq documentation or installed libraries"""

    # Common search terms for fold_right and max
    search_terms = [
        "fold_right",
        "Z.max",
        "List.fold_right",
        "fold_left_max",
        "fold_right_max",
        "maximum",
        "fold_right.*max",
        "Z.max.*fold"
    ]

    print("Potential Coq tactics and lemmas to investigate:")
    print()

    # Suggest approaches
    approaches = [
        "1. Use Z.max_spec and induction on the list",
        "2. Look for List.fold_right_max or similar in List library",
        "3. Use Z.max_lub (least upper bound properties)",
        "4. Create custom lemma using Z.max properties",
        "5. Use Z.max_case_strong for case analysis",
        "6. Apply Z.max_monotone or Z.max_comm properties"
    ]

    for approach in approaches:
        print(approach)

    print()
    print("Key insight: We need to show that fold_right Z.max returns")
    print("the maximum element when that element is present in the list.")
    print()
    print("This can likely be proven by induction on the list structure,")
    print("using the fact that Z.max(a, max_of_rest) = max_of_all")
    print("when a is the maximum element.")

if __name__ == "__main__":
    search_coq_docs()