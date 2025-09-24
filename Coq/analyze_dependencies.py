#!/usr/bin/env python3
"""
Analyze dependencies to find lemmas that are in the wrong files.
"""

import re
from pathlib import Path
from collections import defaultdict

def extract_lemma_definitions(file_path):
    """Extract all lemma/theorem definitions from a Coq file."""
    definitions = {}
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # Pattern to match lemma/theorem definitions
        pattern = r'(?:Lemma|Theorem|Proposition|Corollary|Definition)\s+([\w\']+)'
        matches = re.finditer(pattern, content, re.MULTILINE)

        for match in matches:
            name = match.group(1)
            line_num = content[:match.start()].count('\n') + 1
            definitions[name] = line_num

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return {}

    return definitions

def extract_lemma_usages(file_path, all_lemmas):
    """Extract all references to lemmas in a Coq file."""
    usages = defaultdict(list)
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()

        for line_num, line in enumerate(lines, 1):
            for lemma_name in all_lemmas:
                # Look for lemma usage (not definition)
                if re.search(r'\b' + re.escape(lemma_name) + r'\b', line):
                    # Skip if this line is the definition itself
                    if not re.search(r'(?:Lemma|Theorem|Proposition|Corollary|Definition)\s+' + re.escape(lemma_name), line):
                        usages[lemma_name].append(line_num)

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return {}

    return usages

def main():
    coq_dir = Path("BirdMeertens")
    files_to_check = {
        "BirdMeertens.v": "main",
        "MajorLemmas.v": "major",
        "Lemmas.v": "lemmas",
        "Extra.v": "extra",
        "Extras2.v": "extras2"
    }

    # Extract all definitions
    all_definitions = {}
    all_lemmas = set()

    for file_name, file_type in files_to_check.items():
        file_path = coq_dir / file_name
        if file_path.exists():
            definitions = extract_lemma_definitions(file_path)
            all_definitions[file_type] = definitions
            all_lemmas.update(definitions.keys())

    print("=== DEPENDENCY ANALYSIS ===")
    print(f"Found {len(all_lemmas)} total lemmas/definitions")

    # Check each file for violations
    violations = []

    # Lemmas.v should contain ALL dependencies of MajorLemmas.v except libraries
    major_lemmas_deps = set()
    if "major" in all_definitions:
        major_file = coq_dir / "MajorLemmas.v"
        usages = extract_lemma_usages(major_file, all_lemmas)
        for lemma, lines in usages.items():
            if lemma not in all_definitions["major"]:  # External dependency
                major_lemmas_deps.add(lemma)

    print(f"\nMajorLemmas.v depends on {len(major_lemmas_deps)} external lemmas:")
    for lemma in sorted(major_lemmas_deps):
        # Find where this lemma is defined
        defined_in = None
        for file_type, definitions in all_definitions.items():
            if lemma in definitions:
                defined_in = file_type
                break

        if defined_in != "lemmas":
            print(f"  ❌ {lemma} (defined in {defined_in}, should be in lemmas)")
            violations.append(f"{lemma}: defined in {defined_in}, should be in lemmas")
        else:
            print(f"  ✅ {lemma} (correctly in lemmas)")

    # Check for circular dependencies
    print(f"\nChecking for circular dependencies...")
    lemmas_file = coq_dir / "Lemmas.v"
    lemmas_usages = extract_lemma_usages(lemmas_file, all_lemmas)

    for lemma, lines in lemmas_usages.items():
        if lemma not in all_definitions["lemmas"]:  # External dependency
            defined_in = None
            for file_type, definitions in all_definitions.items():
                if lemma in definitions:
                    defined_in = file_type
                    break

            if defined_in in ["extras2", "extra"]:
                print(f"  ❌ Lemmas.v uses {lemma} from {defined_in} (circular dependency)")
                violations.append(f"Circular: Lemmas.v uses {lemma} from {defined_in}")

    print(f"\n=== SUMMARY ===")
    if violations:
        print(f"❌ Found {len(violations)} dependency violations:")
        for violation in violations:
            print(f"  - {violation}")
        return 1
    else:
        print("✅ No dependency violations found!")
        return 0

if __name__ == "__main__":
    exit(main())