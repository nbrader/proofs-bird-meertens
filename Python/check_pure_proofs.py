#!/usr/bin/env python3

"""
Check which completed theorems are truly pure (have no dependencies on admitted proofs).
Uses Coq's 'Print Assumptions' command to analyze each completed theorem.
"""

import os
import re
import subprocess
import tempfile

def get_completed_theorems():
    """Extract names of all completed theorems (ending in Qed)."""
    base_dir = "Coq/BirdMeertens"
    files = ['BirdMeertens.v', 'Lemmas.v', 'ListFunctions.v', 'ProofStrategy.v', 'FunctionLemmas.v']
    
    completed_theorems = []
    
    for filename in files:
        filepath = os.path.join(base_dir, filename)
        if os.path.exists(filepath):
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Find all theorem/lemma names that end with Qed
            theorem_pattern = r'^((?:Theorem|Lemma|Example)\s+(\w+)[^.]*\.)\s*\n.*?\nQed\.$'
            matches = re.findall(theorem_pattern, content, re.MULTILINE | re.DOTALL)
            
            for full_match, name in matches:
                completed_theorems.append({
                    'name': name,
                    'file': filename,
                    'statement': full_match
                })
    
    return completed_theorems

def check_assumptions_for_theorem(theorem_name):
    """Use Coq to check assumptions for a specific theorem."""
    try:
        # Create a temporary Coq file to check assumptions
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as temp_file:
            temp_file.write(f"""
Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import BirdMeertens.Lemmas.
Require Import BirdMeertens.ListFunctions.
Require Import BirdMeertens.BirdMeertens.

Print Assumptions {theorem_name}.
""")
            temp_filename = temp_file.name
        
        # Run Coq on the temporary file
        result = subprocess.run([
            'coqc', '-Q', 'Coq/BirdMeertens', 'BirdMeertens', 
            '-Q', 'Coq/CoqUtilLib', 'CoqUtilLib',
            '-Q', 'Coq/FreeMonoid', 'FreeMonoid',
            temp_filename
        ], capture_output=True, text=True, cwd='.')
        
        # Clean up
        os.unlink(temp_filename)
        if os.path.exists(temp_filename.replace('.v', '.vo')):
            os.unlink(temp_filename.replace('.v', '.vo'))
        
        # Parse the output for assumptions
        if 'Closed under the global context' in result.stdout:
            return []  # No assumptions
        else:
            # Extract assumption names from output
            lines = result.stdout.split('\n')
            assumptions = []
            for line in lines:
                if ':' in line and not line.startswith('Print'):
                    assumption = line.split(':')[0].strip()
                    if assumption and not assumption.startswith('Axioms'):
                        assumptions.append(assumption)
            return assumptions
            
    except Exception as e:
        return [f"Error: {str(e)}"]

def main():
    print("# PURE PROOF ANALYSIS")
    print("=" * 50)
    print()
    print("Checking which completed theorems have zero dependencies on admitted proofs...")
    print("This may take a moment as we query Coq for each theorem's assumptions.")
    print()
    
    completed_theorems = get_completed_theorems()
    
    pure_proofs = []
    dependent_proofs = []
    
    for theorem in completed_theorems[:5]:  # Test with first 5 theorems
        print(f"Checking {theorem['name']}...", end=" ")
        assumptions = check_assumptions_for_theorem(theorem['name'])
        
        if not assumptions:
            pure_proofs.append(theorem)
            print("PURE ✅")
        else:
            dependent_proofs.append((theorem, assumptions))
            print(f"DEPENDS on {len(assumptions)} assumptions")
    
    print("\n" + "=" * 50)
    print(f"## RESULTS (sample of {len(completed_theorems[:5])} theorems)")
    print(f"- Pure proofs: {len(pure_proofs)}")
    print(f"- Dependent proofs: {len(dependent_proofs)}")
    
    if pure_proofs:
        print(f"\n### PURE PROOFS (No admitted dependencies):")
        for thm in pure_proofs:
            print(f"- **{thm['name']}** ({thm['file']})")
    
    if dependent_proofs:
        print(f"\n### DEPENDENT PROOFS:")
        for thm, assumptions in dependent_proofs:
            print(f"- **{thm['name']}** ({thm['file']}) - depends on: {', '.join(assumptions[:3])}{'...' if len(assumptions) > 3 else ''}")

if __name__ == "__main__":
    main()