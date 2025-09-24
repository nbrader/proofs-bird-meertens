#!/usr/bin/env python3

import re

def find_admits(file_path):
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    admits = []
    for i, line in enumerate(lines):
        if re.search(r'^\s*Admitted\s*\.\s*$', line) or re.search(r'^\s+admit\s*\.\s*(\(\*.*\*\))?\s*$', line):
            print(f"Found admit at line {i+1}: {repr(line)}")
            # Work backwards to find theorem/lemma name
            for j in range(i-1, max(i-50, -1), -1):
                decl_match = re.search(r'^\s*(Lemma|Theorem|Proposition|Corollary)\s+(\w+)', lines[j])
                if decl_match:
                    name = decl_match.group(2)
                    admits.append((name, j + 1))
                    print(f"  Found theorem/lemma: {name} at line {j+1}")
                    break
    return admits

admits = find_admits('Coq/BirdMeertens/TropicalMaxSegSum.v')
print(f"Total admits found: {len(admits)}")