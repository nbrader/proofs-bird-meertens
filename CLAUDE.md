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

## Current Work Status (2025-09-12)

### Completed
- ✅ `nonNegPlus_max_direct` proof in `ProofStrategy.v` (lines 93-150) - Shows that nonNegPlus distributes over Z.max
- ✅ Fixed major compilation issues in `Lemmas.v` - restructured distributivity proof but still has assumption errors

### In Progress - Compilation Issues
- ❌ **COMPILATION BLOCKED**: `nonNegPlus_distributes_over_max` in `Lemmas.v` (lines 237-303) has assumption reference errors
- 🔄 `nonNegPlus_cases` proof in `ProofStrategy.v` (lines 79-90) - Helper lemma for distributivity, needs case analysis completion
- 🔄 `generalised_horners_rule` proof in `Lemmas.v` (lines 307-321) - Key theorem for form equivalence, needs inductive case

### Priority Next Steps
1. **URGENT - Fix compilation**: The `nonNegPlus_distributes_over_max` proof has assumption reference errors at lines 268, 288. Need to debug the proof context and fix the assumptions.
2. **Alternative approach**: Consider using the working proof from `ProofStrategy.v` as template to completely rewrite the broken proof in `Lemmas.v`.
3. **Complete remaining proofs**: Once compilation is fixed, complete the two remaining Admitted proofs.

### Key Files Being Modified
- `Coq/BirdMeertens/ProofStrategy.v` - Helper lemmas and proof strategies (WORKING)
- `Coq/BirdMeertens/Lemmas.v` - Main mathematical lemmas (COMPILATION BROKEN)

### Compilation Status
- ❌ Current build fails at `Lemmas.v:268` with "No such assumption" error
- The proof structure has been partially fixed but assumption contexts are misaligned
- Working proof exists in `ProofStrategy.v` that can be used as reference

### Notes
- The `nonNegPlus_max_direct` proof in `ProofStrategy.v` works correctly with 8-way case analysis
- The same approach attempted in `Lemmas.v` fails due to context/assumption issues
- May need to start fresh with the distributivity proof using the working template