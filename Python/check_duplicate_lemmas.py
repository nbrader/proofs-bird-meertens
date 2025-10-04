#!/usr/bin/env python3
"""
Script to check for duplicate lemmas across Coq files.
Returns exit code 0 if no duplicates found, 1 if any are found.
"""

import os
import re
import sys
from pathlib import Path
from collections import defaultdict

def extract_lemma_names(file_path):
    """Extract all lemma/theorem names from a Coq file."""
    lemma_names = []

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # Pattern to match Lemma/Theorem/Proposition/Corollary declarations
        # Include apostrophes in lemma names
        pattern = r'(?:Lemma|Theorem|Proposition|Corollary|Definition)\s+([\w\']+)'

        matches = re.finditer(pattern, content, re.MULTILINE)

        for match in matches:
            name = match.group(1)
            # Find line number
            lines_before = content[:match.start()].count('\n')
            lemma_names.append((name, lines_before + 1))

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return []

    return lemma_names

def main():
    # Files to check
    coq_dir = Path(__file__).parent / "BirdMeertens"
    files_to_check = [
        coq_dir / "BirdMeertens.v",
        coq_dir / "MajorLemmas.v",
        coq_dir / "Lemmas.v",
        coq_dir / "Extra.v",
        coq_dir / "Extras2.v"
    ]

    # Dictionary to track where each lemma appears
    lemma_locations = defaultdict(list)

    print("Checking for duplicate lemmas...")
    print("=" * 50)

    # Extract lemmas from each file
    for file_path in files_to_check:
        if file_path.exists():
            lemmas = extract_lemma_names(file_path)
            print(f"📁 {file_path.name}: Found {len(lemmas)} lemma(s)/definition(s)")

            for name, line_num in lemmas:
                lemma_locations[name].append((file_path.name, line_num))
        else:
            print(f"⚠️  {file_path.name}: File not found")

    # Check for duplicates
    duplicates_found = False
    print("\n" + "=" * 50)
    print("Duplicate analysis:")

    for lemma_name, locations in lemma_locations.items():
        if len(locations) > 1:
            duplicates_found = True
            print(f"\n❌ DUPLICATE: '{lemma_name}' appears in {len(locations)} files:")
            for file_name, line_num in locations:
                print(f"  - {file_name}:{line_num}")

    print("\n" + "=" * 50)
    if not duplicates_found:
        print("✅ SUCCESS: No duplicate lemmas found across files!")
        return 0
    else:
        print("❌ FAILURE: Duplicate lemmas found!")
        return 1

if __name__ == "__main__":
    sys.exit(main())