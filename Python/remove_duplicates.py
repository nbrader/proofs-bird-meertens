#!/usr/bin/env python3
"""
Script to remove duplicate lemmas from Extras2.v while keeping them in Lemmas.v and MajorLemmas.v.
"""

import re
import sys
from pathlib import Path

def extract_lemma_names_and_content(file_path):
    """Extract lemma names and their full content from a Coq file."""
    lemmas = {}

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()

        # Find all lemma/theorem/definition declarations and their content
        pattern = r'((?:Lemma|Theorem|Proposition|Corollary|Definition)\s+(\w+).*?)(?=(?:Lemma|Theorem|Proposition|Corollary|Definition)\s+\w+|$)'
        matches = re.finditer(pattern, content, re.MULTILINE | re.DOTALL)

        for match in matches:
            name = match.group(2)
            full_content = match.group(1).strip()
            lemmas[name] = full_content

    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return {}

    return lemmas

def get_duplicates():
    """Get list of duplicate lemmas that should be removed from Extras2.v."""
    # These are the duplicates found by our checker script
    duplicates = [
        'map_promotion', 'nonNegPlus_comm', 'fold_scan_fusion_pair', 'generalised_horners_rule',
        'fold_scan_fusion_pair_dual', 'fold_left_ext', 'fold_left_nonNegPlus_eq_max_suffixes',
        'fold_left_right_rev', 'generalised_horners_rule_dual', 'nonNegPlus', 'nonNegSum',
        'nonNegSum_dual', 'nonNegMaximum', 'nonNegMaximum_dual', 'maxSoFarAndPreviousSum',
        'maxSoFarAndPreviousSum_dual', 'nonNegPlus_nonneg', 'nonNegSum_dual_nonneg',
        'app_concat', 'fold_max_nonneg', 'fold_max_app', 'tropical_horner_eq_nonNegPlus',
        'fold_left_monotonic_nonNegPlus', 'nonNegSum_dual_suffix_le', 'inits_cons',
        'inits_contains_original', 'inits_are_prefixes', 'nonNegSum_prefix_le',
        'tails_are_suffixes', 'fold_left_right_equiv', 'max_fold_duality',
        'max_fold_duality_zero', 'fold_promotion', 'fold_promotion_dual',
        'fold_right_max_le', 'fold_right_max_returns_max', 'fold_left_max_returns_max',
        'fold_right_ext', 'map_distr', 'max_add_distributes', 'fold_left_max_init_distrib',
        'scan_head', 'fold_left_Z_max_monotonic', 'fold_scan_fusion_pair_general',
        'fold_right_nonNegPlus_eq_max_prefixes'
    ]
    return duplicates

def remove_duplicates_from_extras2():
    """Remove duplicate lemmas from Extras2.v."""
    extras2_path = Path("BirdMeertens/Extras2.v")

    if not extras2_path.exists():
        print(f"Error: {extras2_path} not found!")
        return False

    # Read the current content
    with open(extras2_path, 'r', encoding='utf-8') as f:
        content = f.read()

    duplicates_to_remove = get_duplicates()
    removed_count = 0

    # For each duplicate, find and remove its definition/lemma from Extras2.v
    for lemma_name in duplicates_to_remove:
        # Pattern to match the entire lemma/definition including its proof
        pattern = r'(?:^|\n)((?:Lemma|Theorem|Proposition|Corollary|Definition)\s+' + re.escape(lemma_name) + r'\b.*?)(?=\n(?:Lemma|Theorem|Proposition|Corollary|Definition|\(\*|\Z))'

        matches = list(re.finditer(pattern, content, re.MULTILINE | re.DOTALL))

        if matches:
            # Remove all occurrences (there might be multiple)
            for match in reversed(matches):  # Remove from end to preserve indices
                content = content[:match.start()] + content[match.end():]
                removed_count += 1
                print(f"Removed {lemma_name} from Extras2.v")

    # Write the cleaned content back
    with open(extras2_path, 'w', encoding='utf-8') as f:
        f.write(content)

    print(f"\nTotal duplicates removed: {removed_count}")
    return True

def main():
    if remove_duplicates_from_extras2():
        print("Successfully removed duplicates from Extras2.v")
        print("Please run check_duplicate_lemmas.py to verify no duplicates remain")
        return 0
    else:
        print("Failed to remove duplicates")
        return 1

if __name__ == "__main__":
    sys.exit(main())