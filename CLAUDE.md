# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Coq formalization project that proves the correctness of Kadane's algorithm for the Maximum subarray problem using a generalized semiring-based approach. The project demonstrates that **Kadane's algorithm is fundamentally algebraic**, with **100% of its derivation (all 8 steps)** using only general semiring properties and structural laws.

### Project Status: Core Derivation Complete

**MAJOR ACHIEVEMENT**: The generalized semiring-based derivation is **complete**. All 8 forms (gform1 through gform8) have been proven equivalent using:
1. General semiring axioms (associativity, identities, distributivity)
2. List manipulation laws
3. Fold-scan fusion law (proven with zero additional assumptions)

See `Coq/KadanesAlgorithm/KadanesAlgorithm.v` for the complete derivation.

### Project Architecture

**ARCHITECTURE STRATEGY**:
- **`KadanesAlgorithm/` directory**: Contains the COMPLETED primary proof framework
  - `KadanesAlgorithm.v`: Complete general semiring-based proofs (gform1-gform8) that work for ANY semiring
  - Specific instances like `MaxSubarrayKadane.v` that instantiate the framework for particular semirings
  - This represents the MAIN theoretical contribution of the project

- **`BirdMeertens/` directory**: Contains the ORIGINAL integer-specific proofs
  - Retained for reference and historical purposes
  - Demonstrates the concrete integer case with explicit intermediate forms
  - Provides useful lemmas/techniques for other purposes
  - Not used as dependencies for `KadanesAlgorithm/` proofs

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

### Historical Note: Tropical Semiring Proof Strategy

**NOTE**: This section describes the historical approach used in the original `BirdMeertens/` proofs. The completed `KadanesAlgorithm/` framework supersedes this by proving the result directly for all semirings.

The original approach dealt with non-semiring clamped operations by:
1. Recognizing that `nonNegPlus` with zero-clamping doesn't form a proper semiring
2. Using case-based reasoning (all non-negative, all non-positive, mixed cases)
3. Bridging to the tropical semiring framework for the mixed case

This is no longer necessary in the generalized framework, which works directly with proper semiring operations.

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

## Generalized Semiring-Based Kadane's Algorithm

### Overview
The `Coq/KadanesAlgorithm/` directory contains a generalized semiring-based formulation of Kadane's algorithm that abstracts away from specific operations (max/plus) to work with arbitrary semirings.

### Key Design Principles
1. **Pure Semiring Operations**: Uses existing semiring infrastructure from `FreeMonoid.StructSemiring`
2. **Sum/Product Terminology**:
   - "Sum" operations use ⊕ (semiring addition, e.g., max in max-plus semiring)
   - "Product" operations use ⊗ (semiring multiplication, e.g., + in max-plus semiring)
3. **Direct Operations**: No lifting functions - operates directly on semiring elements
4. **Abstract Framework**: All forms parameterized by semiring type `{A : Type} `{Semiring A}`

### Eight Equivalent Forms (gform1-gform8) - COMPLETED
The generalized formulation proves equivalence of all 8 forms using only semiring properties:
- **gform1**: `semiring_sum ∘ map semiring_product ∘ segs` (specification)
- **gform2-gform4**: List manipulation and fold promotion
- **gform5-gform6**: Horner's rule transformation (uses `generalised_horners_rule_right`)
- **gform6-gform7**: Scan-fold relationship
- **gform7-gform8**: Fold-scan fusion (NO additional assumptions required!)

### Key Results
1. **gform5 → gform6**: Uses generalized Horner's rule from `FreeMonoid.SemiringLemmas` - works for ANY semiring
2. **gform7 → gform8**: Uses fold-scan fusion law proven with zero assumptions - purely structural
3. **Main Theorem**: `Generalized_Kadane_Correctness: gform1 = gform8` - proven in `KadanesAlgorithm.v:356`

### Current and Future Work
The core derivation is complete. Remaining work includes:
1. Creating specific semiring instances in separate files:
   - `MaxSubarrayKadane.v` for tropical (max-plus) semiring
   - Potential future instances: Boolean semiring, other semirings
2. Connecting instances to `BirdMeertens.v` integer-specific proofs for validation
3. Exploring dual (fold_left) versions of the algorithm

### Benefits of This Approach
- **Complete Generality**: Works for ANY semiring, not just integers or tropical
- **Mathematical Clarity**: Makes algebraic structure explicit
- **Broader Applicability**: Same framework for different problem domains
- **Clean Proofs**: Leverages existing semiring theory from `FreeMonoid.SemiringLemmas`
