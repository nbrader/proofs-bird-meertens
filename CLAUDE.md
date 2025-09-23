# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Coq formalization project that translates a theorem from the Bird-Meertens Formalism Wikipedia article about the correctness of Kadane's algorithm for the Maximum subarray problem.

## Key Proof Strategy: Dual Conversion Approach

**IMPORTANT**: When proving dual theorems (theorems that convert between fold_left/scan_left and fold_right/scan_right), use the **dual conversion approach**:

1. **Start with the original theorem** that uses fold_right/scan_right operations
2. **Apply dual conversion theorems** like `fold_left_rev_right`, `fold_left_right_rev`, `scan_left_right_rev` to convert between left and right operations
3. **Handle argument order differences** - the dual operations often have reversed argument order (e.g., `(x <#> v)` vs `(v <#> x)`)
4. **Create missing conversion theorems** if needed for specific operations like Z.max, nonNegPlus, etc.

## Essential Commands

### Building the Project
- `./build_coq.sh` - Primary build command (run from the Coq/ directory)
- If line endings are problematic: `dos2unix build_coq.sh` first
- The build script generates a Makefile from `_CoqProject` and runs `make`

### Development Setup
- Requires Visual Studio Code (1.94.2) with VsCoq extension (v2.1.2)
- Open the folder containing `.v` files directly in VSCode (not parent folders) for proper file resolution
- May require submodule initialization after cloning: run "Submodule Update"

### Git Submodule Management
**CRITICAL**: When making changes to submodules (CoqUtilLib, FreeMonoid), follow this commit sequence:
1. **First commit changes within the submodule directory**:
   ```bash
   cd Coq/CoqUtilLib  # or Coq/FreeMonoid
   git add .
   git commit -m "Your changes"
   git push
   ```
2. **Then commit the submodule update in the main repository**:
   ```bash
   cd ../..  # Return to main repo root
   git add Coq/CoqUtilLib  # or Coq/FreeMonoid
   git commit -m "Update submodule with your changes"
   git push
   ```
3. **NEVER commit submodule changes without first committing within the submodule** - this creates dangling references

### Python Analysis Tools
**NOTE**: Use `python3` for all Python commands (not `python`)
- `python3 Python/references.py` - Generates dependency graph in TGF format
- `python3 Python/completed_proofs_report.py` - Reports on completed proofs (100% completion)
- `python3 Python/theorem_catalog.py` - Catalogs theorem definitions by category

## Code Architecture

### Coq Structure
The main Coq development is in `Coq/BirdMeertens/` with the following module organization:

1. **BirdMeertens.v** - Main theorem proving Kadane's algorithm correctness through 8 equivalent forms
2. **MajorLemmas.v** - Theorems that BirdMeertens.v depends on immediately (direct dependencies not in libraries)
3. **Lemmas.v** - Theorems that BirdMeertens.v depends on indirectly (dependencies of MajorLemmas.v)
4. **Extra.v** - Results that aren't necessary for the main theorems (unused by BirdMeertens.v)

**Additional Libraries:**
- **CoqUtilLib** - Utility functions for list operations and functional programming  
- **FreeMonoid** - Comprehensive monoid theory with examples and structural definitions

### Key Mathematical Concepts
The project proves equivalence through transformational forms:
- `form1` through `form8` represent different but equivalent formulations
- Each form transformation is proven as a separate theorem
- Final form (`form8`) represents Kadane's efficient algorithm

### Supporting Languages
- **Haskell/** - Reference implementations and benchmarking
- **Python/** - Analysis tools for dependency tracking and visualization
- **Rough Working/** - Development notes and diagrams

The project structure allows for cross-language validation of the formal Coq proofs against executable Haskell implementations.

### Tropical Semiring Proof Strategy for nonneg_tropical_fold_right_returns_max (and ultimately the form5 to form6 step)

**Proof Strategy**:
1. **Recognize non-semiring nature**: `nonNegPlus` with zero-clamping doesn't form a proper semiring, so direct application of generalized Horner's rule fails
2. **Case-based approach for Kadane's algorithm**:
   - **All non-negative case**: Maximum subarray is the entire array (trivial)
   - **All non-positive case**: Maximum subarray is the singleton of the largest element
   - **Mixed case**: Use tropical semiring Horner's rule where maximum subarray sum is guaranteed ≥ 0
3. **Tropical semiring without clamping**: For the mixed case, prove the proper tropical semiring version where the identity constraints are satisfied
4. **Bridge to clamped version**: Show that for inputs where the maximum is ≥ 0, the clamped and unclamped versions are equivalent

**PLEASE NOTE**:
- Run tropical_insight.hs for insight into this.
- In the mixed case, nonNegSum xs >= 0 by definition (nonNegSum always returns >= 0)
- This allows us to bridge to the tropical semiring framework
- The idea is to prove this using tropical_horners_rule (proved in the library files) along with thefact that the non-negative clamped functions are equal to their regular versions when the result would have been non-negative anyway.

**Implementation Plan**:
- Prove `nonneg_tropical_fold_right_returns_max` directly using existing proof techniques (already proven)
- Create separate tropical semiring instance without zero-clamping for theoretical completeness
- Document the case split strategy for applying this result in the main Kadane's algorithm proof

### Proof Development Strategy
**CRITICAL**: When working on complex proofs, use computational verification at each step:
1. **Write fresh Python scripts** to test each intermediate goal before attempting Coq proof
2. **Never trust existing Python scripts** - they may not test what you currently intend to prove
3. **Test each subgoal independently** with targeted computational verification
4. **Incrementally build proofs** only after Python verification confirms the goal is viable
5. **Create new verification scripts** for each proof attempt to ensure accuracy

### Interactive Proof Debugging
**IMPORTANT**: When working on complex Coq proofs and unsure of goal structure:
1. **Ask the user to show intermediate goals** - The user has GUI access to VSCode with VsCoq extension that shows goals at every tactic step
2. **Be specific about which step** - Ask to see the goal "after applying tactic X but before tactic Y"
3. **Don't guess goal structure** - If unsure what the goal looks like after `simpl`, `rewrite`, etc., ask rather than assume
4. **Verify rewrite targets match** - Many proof failures occur because rewrite patterns don't match the actual goal structure
5. **Use this for debugging failed tactics** - When tactics fail with "no subterm matching" errors, ask to see the actual goal

**Example**: "Could you show me what the goal looks like after `simpl fold_left` but before the `rewrite` step? I want to make sure I understand the exact structure."

### Proof Completion Requirements
**CRITICAL**: When working on admitted proofs, follow these strict guidelines:
1. **Never remove an admitted proof without first proving it untrue**
2. To decrease admitted proof count, you must either:
   - Complete the proof with a valid proof ending in `Qed.`
   - Prove the statement is false/contradictory and then remove it with a comment explaining why
3. **Do not simply delete or comment out admitted proofs** - this is incorrect methodology
4. Always verify the admitted count decreases through legitimate proof completion
5. **Never declare a theorem "established" or "proven" if it uses `Admitted`** - this is false and misleading
6. **NEVER introduce new `Admitted` lemmas during refactoring or reorganization** - this is a regression that decreases proof quality
7. **When reorganizing theorems between files, preserve all existing proofs with `Qed.`** - do not admit working proofs

### Theorem Extraction Verification
**CRITICAL**: When extracting theorems to separate files (like MajorLemmas.v), ALWAYS verify the target file contains actual theorem statements, not just comments:
1. **Check that theorem files contain actual `Lemma`/`Theorem` statements with `Proof...Qed.`**
2. **Never accept files that only contain comments about theorems** - this defeats the purpose of extraction
3. **Use `Grep` to verify theorem statements exist**: `grep "^Lemma\|^Theorem" target_file.v`
4. **If the file only contains `(* comments *)` and `Require` statements, the extraction failed**
5. **MANDATORY CHECK**: After any theorem extraction, verify the file has actual executable theorem code
6. **Document this check requirement** in any instructions about theorem organization

### Lemmas.v Dependency Requirements
**CRITICAL**: When reorganizing theorems for MajorLemmas.v dependencies, follow these specific rules:
1. **Lemmas.v must contain ALL dependencies of MajorLemmas.v** - both direct and indirect dependencies
2. **EXCLUDE only library dependencies**: Do not include theorems from CoqUtilLib, FreeMonoid, or standard Coq libraries
3. **Include ALL non-library dependencies**: If MajorLemmas.v uses theorem A, and theorem A uses theorem B (non-library), then Lemmas.v must contain both A and B
4. **Complete dependency closure**: Lemmas.v should be self-contained for all non-library dependencies
5. **No duplication with Extra.v files**: Remove any theorems from Extra.v that are in any other file
6. **Library imports remain**: Keep all `Require Import` statements for external libraries in both files as needed
