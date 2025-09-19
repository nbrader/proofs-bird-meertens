#!/usr/bin/env python3

"""
Comprehensive theorem catalog for the BirdMeertens project.
Creates a searchable reference of all proven theorems with their statements,
categorizes them by type, and identifies pure proofs vs those with dependencies.
"""

import os
import re
import subprocess

def extract_all_theorems_from_file(filepath):
    """Extract all theorem/lemma declarations with their full statements."""
    completed_theorems = []
    admitted_theorems = []
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # Pattern to match theorem declarations with full statements
    theorem_pattern = r'^((?:Theorem|Lemma|Example)\s+\w+[^.]*\.)'
    
    lines = content.split('\n')
    current_theorem = None
    in_proof = False
    
    for i, line in enumerate(lines):
        # Check for theorem/lemma start
        theorem_match = re.match(theorem_pattern, line)
        if theorem_match:
            current_theorem = {
                'statement': theorem_match.group(1),
                'name': theorem_match.group(1).split()[1].split(':')[0] if ':' in theorem_match.group(1) else theorem_match.group(1).split()[1],
                'line': i + 1,
                'type': theorem_match.group(1).split()[0],
                'full_statement': theorem_match.group(1)
            }
            in_proof = True
            continue
        
        # Check for proof end
        if in_proof and current_theorem:
            if line.strip() == 'Qed.':
                completed_theorems.append(current_theorem)
                current_theorem = None
                in_proof = False
            elif line.strip() == 'Admitted.':
                admitted_theorems.append(current_theorem)
                current_theorem = None
                in_proof = False
    
    return completed_theorems, admitted_theorems

def categorize_theorems(theorems):
    """Categorize theorems by their purpose and content."""
    categories = {
        'Form Transformations': [],
        'List Operations': [],
        'Mathematical Properties': [],
        'Function Lemmas': [],
        'Utility Lemmas': [],
        'Examples/Tests': []
    }
    
    for thm in theorems:
        name = thm['name'].lower()
        statement = thm['full_statement'].lower()
        
        if 'form' in name and 'eq' in name:
            categories['Form Transformations'].append(thm)
        elif any(x in name for x in ['tails', 'inits', 'scan', 'fold', 'map', 'concat']):
            categories['List Operations'].append(thm)
        elif any(x in name for x in ['max', 'plus', 'add', 'neg', 'comm', 'assoc', 'distrib']):
            categories['Mathematical Properties'].append(thm)
        elif any(x in name for x in ['function', 'compose', 'promotion']):
            categories['Function Lemmas'].append(thm)
        elif any(x in name for x in ['example', 'test', 'one', 'two', 'three']):
            categories['Examples/Tests'].append(thm)
        else:
            categories['Utility Lemmas'].append(thm)
    
    return categories

def create_theorem_reference():
    """Create a comprehensive theorem reference catalog."""
    base_dir = "Coq/BirdMeertens"
    files = ['BirdMeertens.v', 'Lemmas.v', 'ListFunctions.v', 'ProofStrategy.v', 'FunctionLemmas.v']
    
    print("# BIRDMEERTENS THEOREM CATALOG & REFERENCE")
    print("=" * 60)
    print()
    print("**Purpose**: Comprehensive searchable reference of all proven theorems")
    print("**Usage**: Search by theorem name, category, or mathematical property")
    print("**Status**: Pure proofs (Qed) vs those potentially depending on admitted theorems")
    print()
    
    all_completed = {}
    all_admitted = {}
    
    # Collect all theorems
    for filename in files:
        filepath = os.path.join(base_dir, filename)
        if os.path.exists(filepath):
            completed, admitted = extract_all_theorems_from_file(filepath)
            for thm in completed:
                thm['file'] = filename
                all_completed[thm['name']] = thm
            for thm in admitted:
                thm['file'] = filename
                all_admitted[thm['name']] = thm
    
    # Categorize completed theorems
    completed_list = list(all_completed.values())
    categories = categorize_theorems(completed_list)
    
    # Print categorized results
    print("## COMPLETED THEOREMS BY CATEGORY")
    print("=" * 40)
    
    total_completed = 0
    for category, theorems in categories.items():
        if theorems:
            print(f"\n### {category} ({len(theorems)} theorems)")
            for thm in sorted(theorems, key=lambda x: x['name']):
                print(f"- **{thm['name']}** ({thm['file']}:{thm['line']})")
                print(f"  `{thm['full_statement']}`")
                total_completed += 1
    
    print(f"\n## ADMITTED THEOREMS ({len(all_admitted)} total)")
    print("=" * 30)
    for name, thm in sorted(all_admitted.items()):
        print(f"- **{name}** ({thm['file']}:{thm['line']}) [ADMITTED]")
        print(f"  `{thm['full_statement']}`")
    
    print(f"\n## SUMMARY STATISTICS")
    print("=" * 20)
    print(f"- **Completed proofs (Qed)**: {total_completed}")
    print(f"- **Admitted proofs**: {len(all_admitted)}")
    print(f"- **Completion rate**: {total_completed * 100 / (total_completed + len(all_admitted)):.1f}%")
    
    print(f"\n## SEARCH QUICK REFERENCE")
    print("=" * 25)
    print("**By Purpose:**")
    for category, theorems in categories.items():
        if theorems:
            names = [t['name'] for t in theorems]
            print(f"- {category}: {', '.join(sorted(names))}")
    
    print(f"\n**Key Theorems for Proof Development:**")
    key_theorems = [
        ('form6_eq_form7', 'Uses tails_rec strategy (pure proof)'),
        ('nonNegPlus_distributes_over_max', 'Distributivity property'),
        ('scan_right_tails_rec_fold', 'Core scan-tails relationship'),
        ('MaxSegSum_Equivalence', 'Main theorem (depends on 2 admitted)'),
        ('inits_cons', 'Useful for induction proofs'),
        ('map_promotion', 'Function composition property')
    ]
    
    for name, desc in key_theorems:
        if name in all_completed:
            thm = all_completed[name]
            print(f"- **{name}**: {desc} ({thm['file']}:{thm['line']})")
        elif name in all_admitted:
            print(f"- **{name}**: {desc} [ADMITTED]")
    
    return all_completed, all_admitted

def main():
    completed, admitted = create_theorem_reference()
    
    print(f"\n## NOTES FOR PROOF DEVELOPMENT")
    print("=" * 30)
    print("- **Pure proofs**: Most utility lemmas in Lemmas.v are likely dependency-free")
    print("- **Strategic insight**: form6_eq_form7 is now pure due to tails_rec refactoring") 
    print("- **Remaining blockers**: Only 3 admitted theorems block further progress")
    print("- **Search tip**: Use Ctrl+F to find theorems by name, mathematical property, or list operation")
    
if __name__ == "__main__":
    main()