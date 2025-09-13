# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Coq formalization project that translates theorem from the Bird-Meertens Formalism Wikipedia article about the correctness of Kadane's algorithm for the Maximum subarray problem.

## Essential Commands

### Building the Project
- `./build_coq.sh` - Primary build command (run from the Coq/ directory)
- If line endings are problematic: `dos2unix build_coq.sh` first
- The build script generates a Makefile from `_CoqProject` and runs `make`

### Development Setup
- Requires Visual Studio Code (1.94.2) with VsCoq extension (v2.1.2)
- Open the folder containing `.v` files directly in VSCode (not parent folders) for proper file resolution
- May require submodule initialization after cloning: run "Submodule Update"

### Python Analysis Tools
- `python Python/references.py` - Generates dependency graph in TGF format
- `python Python/summarize_dependencies.py` - Analyzes Coq dependencies

## Code Architecture

### Coq Structure
The main Coq development is in `Coq/BirdMeertens/` with four key modules:

1. **ListFunctions.v** - Core list manipulation functions (`tails`, `inits`, `segs`, `scan_right`, etc.)
2. **Lemmas.v** - Mathematical definitions and operations (`nonNegPlus`, `nonNegSum`, `nonNegMaximum`) 
3. **FunctionLemmas.v** - Supporting lemmas for functions
4. **BirdMeertens.v** - Main theorem proving Kadane's algorithm correctness through 8 equivalent forms

### Module Dependencies
- `BirdMeertens.v` imports `Lemmas.v` and `ListFunctions.v`
- `Lemmas.v` imports `ListFunctions.v` and `FunctionLemmas.v`
- All modules use standard Coq libraries (Program.Basics, Lists.List, ZArith, etc.)

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

## Current Work Status (2025-09-13)

### Completed
- ✅ All modules now compile successfully (`ListFunctions.v`, `FunctionLemmas.v`, `Lemmas.v`, `BirdMeertens.v`, `ProofStrategy.v`)
- ✅ Fixed compilation issues in `Lemmas.v` - assumption reference errors resolved
- ✅ `leb_max_simple` proof in `ProofStrategy.v:56-85` - Boolean consistency lemma proving that if max(s+x, t+x) ≥ 0 then either s+x ≥ 0 or t+x ≥ 0
- ✅ `nonNegPlus_distributes_over_max` proof in `Lemmas.v:186-247` - **COMPLETED**: Proves distributivity of nonNegPlus over Z.max using exhaustive case analysis
- ✅ `nonNegPlus_cases` proof in `ProofStrategy.v:89-152` - **COMPLETED**: Detailed case analysis showing nonNegPlus behavior under different sign combinations

### Development Status
- ✅ **COMPILATION WORKING**: All Coq modules compile without errors
- 🔄 Some proofs may still use `Admitted` - check individual files for remaining proof obligations
- 🔄 Complete formal verification may require finishing any remaining admitted lemmas

### Remaining Admitted Proofs Analysis

After completing `leb_max_simple`, analysis of remaining admitted proofs shows they require advanced mathematical reasoning:

**Complex Proofs (Require Expertise):**
- `generalised_horners_rule` in `Lemmas.v:313` - Key theorem for Bird-Meertens formalism equivalences
- `scan_lemma` in `Lemmas.v:323` - Complex scan/fold relationship  
- `fold_scan_fusion` in `Lemmas.v:327` - Advanced scan fusion property
- Form equivalence theorems in `BirdMeertens.v` (`form5_eq_form6`, `form6_eq_form7`, `form7_eq_form8`) - High-level mathematical transformations

**Recently Completed:**
- ✅ `nonNegPlus_distributes_over_max` in `Lemmas.v:186-247` - Distributivity of nonNegPlus over Z.max, moved from ProofStrategy and completed
- ✅ `nonNegPlus_cases` in `ProofStrategy.v:89-152` - Detailed case analysis of nonNegPlus behavior under different sign combinations using lia tactic

**Proof Complexity Notes:**
- Boolean/proposition conversions between `Z.leb` and `Z.le` require careful handling
- Case analysis on multiple boolean conditions creates complex proof obligations
- Max distribution properties need intricate mathematical reasoning
- Most proofs depend on completing foundational lemmas first

### Key Files
- `Coq/BirdMeertens/ProofStrategy.v` - Helper lemmas and proof strategies
- `Coq/BirdMeertens/Lemmas.v` - Main mathematical lemmas 
- `Coq/BirdMeertens/BirdMeertens.v` - Main theorem proving Kadane's algorithm correctness
- `Coq/BirdMeertens/ListFunctions.v` - Core list manipulation functions
- `Coq/BirdMeertens/FunctionLemmas.v` - Supporting lemmas for functions

### Compilation Status
- ✅ Current build succeeds: `make clean && make` completes without errors
- All `.v` files compile in correct dependency order
- Build system generates proper Makefile from `_CoqProject`