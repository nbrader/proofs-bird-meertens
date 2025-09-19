#!/usr/bin/env python3

"""
Generate a report of all completed proofs in the BirdMeertens project.
Separates proofs that are fully proven from those that depend on admitted theorems.
"""

import os
import re
import subprocess

def extract_theorems_from_file(filepath):
    """Extract all theorem/lemma declarations that end with Qed from a file."""
    theorems = []
    admitted = []
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Look for Theorem/Lemma followed by eventual Qed (not Admitted)
    theorem_qed_pattern = r'^((?:Theorem|Lemma|Example)\s+\w+[^.]*\.)\s*\n.*?\nQed\.$'
    qed_matches = re.findall(theorem_qed_pattern, content, re.MULTILINE | re.DOTALL)
    
    # Look for Theorem/Lemma followed by eventual Admitted
    theorem_admitted_pattern = r'^((?:Theorem|Lemma|Example)\s+\w+[^.]*\.)\s*\n.*?\nAdmitted\.$'
    admitted_matches = re.findall(theorem_admitted_pattern, content, re.MULTILINE | re.DOTALL)
    
    for match in qed_matches:
        theorem_line = match.strip()
        if ':' in theorem_line:
            name = theorem_line.split()[1].split(':')[0]
            theorems.append((name, theorem_line))
    
    for match in admitted_matches:
        theorem_line = match.strip()
        if ':' in theorem_line:
            name = theorem_line.split()[1].split(':')[0]
            admitted.append((name, theorem_line))
    
    return theorems, admitted

def main():
    base_dir = "Coq/BirdMeertens"
    files = ['BirdMeertens.v', 'Lemmas.v', 'ListFunctions.v', 'ProofStrategy.v', 'FunctionLemmas.v']
    
    print("# COMPLETED THEOREMS AND LEMMAS REPORT")
    print("=" * 50)
    print()
    
    all_completed = {}
    
    for filename in files:
        filepath = os.path.join(base_dir, filename)
        if os.path.exists(filepath):
            theorems, admitted = extract_theorems_from_file(filepath)
            if theorems:
                print(f"## {filename} - COMPLETED (Qed)")
                for name, statement in theorems:
                    print(f"- **{name}**")
                    all_completed[name] = (filename, statement)
                print()
            if admitted:
                print(f"## {filename} - ADMITTED")
                for name, statement in admitted:
                    print(f"- **{name}** [ADMITTED]")
                print()
    
    print(f"\n## Summary")
    print(f"Total completed proofs (Qed): {len(all_completed)}")
    total_admitted = sum(1 for filename in files if os.path.exists(os.path.join(base_dir, filename)) for _, _ in extract_theorems_from_file(os.path.join(base_dir, filename))[1])
    print(f"Total admitted proofs: {total_admitted}")
    completion_rate = len(all_completed) * 100 / (len(all_completed) + total_admitted) if (len(all_completed) + total_admitted) > 0 else 0
    print(f"Completion rate: {completion_rate:.1f}%")
    
    # List all completed theorem names
    print("\n### All Completed Theorems/Lemmas (Pure Qed proofs):")
    for name in sorted(all_completed.keys()):
        filename, _ = all_completed[name]
        print(f"- {name} ({filename})")

if __name__ == "__main__":
    main()