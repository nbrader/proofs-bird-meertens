# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Coq formalization project that translates a theorem from the Bird-Meertens Formalism Wikipedia article about the correctness of Kadane's algorithm for the Maximum subarray problem.

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
- `python check_pure_proofs.py` - THIS SHOULD BE MOVED TO THE PYTHON FOLDER AND MADE TO WORK FROM THERE
- `python completed_proofs_report.py` - THIS SHOULD BE MOVED TO THE PYTHON FOLDER AND MADE TO WORK FROM THERE
- `python theorem_catalog.py` - THIS SHOULD BE MOVED TO THE PYTHON FOLDER AND MADE TO WORK FROM THERE
- THERE ARE ALSO SHELL AND BATCH SCRIPTS WHICH SHOULD BE MOVED TO THE RELEVANT PLACES.

## Code Architecture

### Coq Structure
The main Coq development is in `Coq/BirdMeertens/` with four key modules:

1. **ListFunctions.v** - Core list manipulation functions (`tails`, `inits`, `segs`, `scan_right`, etc.)
2. **Lemmas.v** - Mathematical definitions and operations (`nonNegPlus`, `nonNegSum`, `nonNegMaximum`) 
3. **FunctionLemmas.v** - Supporting lemmas for functions
4. **BirdMeertens.v** - Main theorem proving Kadane's algorithm correctness through 8 equivalent forms
5. **ProofStrategy.v** - A temporary file which should have any useful contents moved out of it before being removed.

2 library folders I'm hoping to make use of:
Added **CoqUtilLib** - Utility functions for list operations and functional programming  
Added **FreeMonoid** - Comprehensive monoid theory with examples and structural definitions

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

### Code Duplication Analysis

**⚠️ Critical Issue Identified**: Parallel development has occurred in `ListFunctions.v`:
- Main project: `Coq/BirdMeertens/ListFunctions.v` 
- Library: `Coq/CoqUtilLib/ListFunctions.v`
- **Identical definitions**: `tails`, `inits`, `scan_right`, `scan_left`
- **Divergent capabilities**: Library has `take_n`/`drop_n`, main project has Bird-Meertens specific lemmas

**Recommendation**: Consolidate to avoid maintenance issues - see `LIBRARY_INTEGRATION_ANALYSIS.md` for detailed plan.

### Progress Made with Libraries
- `MonoidConcat.v` provides `mconcat` operations relevant for fold proofs
- Multiple monoid instances could help with `fold_scan_fusion`
- Rich theoretical framework available for remaining fold-related proofs

**Previous Core Structural Issue** (Now Eliminated):
The complex `fold_right` definition of `tails` created structural proof difficulties:

```coq
Definition tails {A : Type}: list A -> list (list A) := fold_right (fun x xsxss => match xsxss with
  | [] => [[]] (* This case is impossible. *)
  | xs :: xss => (x::xs) :: (xs::xss)
end) [[]].
```

**Strategic Solution Applied:**
Instead of proving `tails_rec_equiv`, we redefined `form6` to use the simpler `tails_rec`:
```coq
Fixpoint tails_rec {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' => xs :: tails_rec xs'
  end.
```

**Impact**: Eliminated complex structural induction requirements and unification errors.

### Proof Completion Requirements
**CRITICAL**: When working on admitted proofs, follow these strict guidelines:
1. **Never remove an admitted proof without first proving it untrue**
2. To decrease admitted proof count, you must either:
   - Complete the proof with a valid proof ending in `Qed.`
   - Prove the statement is false/contradictory and then remove it with a comment explaining why
3. **Do not simply delete or comment out admitted proofs** - this is incorrect methodology
4. Always verify the admitted count decreases through legitimate proof completion
