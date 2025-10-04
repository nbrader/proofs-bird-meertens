#!/usr/bin/env python3
"""
Script to check for admitted lemmas in Coq files.
Returns exit code 0 if no admitted lemmas found, 1 if any are found.
"""

import os
import re
import sys
from pathlib import Path

def find_admitted_lemmas(file_path):
    """Find all admitted lemmas/theorems in a Coq file."""
    admitted_items = []

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        # Look for "Admitted." and "admit." and work backwards to find the theorem/lemma name
        for i, line in enumerate(lines):
            if re.search(r'^\s*Admitted\s*\.\s*$', line) or re.search(r'^\s+admit\s*\.\s*(\(\*.*\*\))?\s*$', line):
                # Work backwards to find the theorem/lemma declaration
                for j in range(i-1, max(i-50, -1), -1):  # Look back up to 50 lines for admit tactics
                    decl_match = re.search(r'^\s*(Lemma|Theorem|Proposition|Corollary)\s+(\w+)', lines[j])
                    if decl_match:
                        keyword = decl_match.group(1)
                        name = decl_match.group(2)
                        admitted_items.append((name, j + 1))  # Line numbers are 1-based
                        break

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return []

    return admitted_items

def main():
    # Files to check
    coq_dir = Path(__file__).parent / "BirdMeertens"
    files_to_check = [
        coq_dir / "BirdMeertens.v",
        coq_dir / "MajorLemmas.v",
        coq_dir / "Lemmas.v",
        coq_dir / "Extra.v",
        coq_dir / "TropicalMaxSegSum.v"
    ]

    total_admitted = 0

    print("Checking for admitted lemmas...")
    print("=" * 50)

    for file_path in files_to_check:
        if file_path.exists():
            admitted = find_admitted_lemmas(file_path)
            if admitted:
                print(f"\n❌ {file_path.name}:")
                for name, line_num in admitted:
                    print(f"  Line {line_num}: {name}")
                total_admitted += len(admitted)
            else:
                print(f"✅ {file_path.name}: No admitted lemmas")
        else:
            print(f"⚠️  {file_path.name}: File not found")

    print("\n" + "=" * 50)
    if total_admitted == 0:
        print("✅ SUCCESS: No admitted lemmas found in any file!")
        return 0
    else:
        print(f"❌ FAILURE: Found {total_admitted} admitted lemma(s) total")
        return 1

if __name__ == "__main__":
    sys.exit(main())