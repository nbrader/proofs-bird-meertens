# BIRDMEERTENS THEOREM REFERENCE CATALOG

**Purpose**: Quick searchable reference for all theorems and lemmas  
**Usage**: Search by theorem name, mathematical property, or list operation  

---

## 📊 PROJECT STATUS

**MAJOR ACHIEVEMENT**: The generalized semiring-based proof framework is **COMPLETE**!

**Core Result**: `Coq/KadanesAlgorithm/KadanesAlgorithm.v` contains a complete proof that Kadane's algorithm (gform8) equals the specification (gform1) for **ANY semiring** - not just integers or tropical semirings.

**Note**: This file documents the original `BirdMeertens/` integer-specific proofs. The generalized framework in `KadanesAlgorithm/` supersedes this approach by proving the result for all semirings at once.

---

## 🎯 FORM TRANSFORMATIONS (Bird-Meertens Algorithm Chain)

**Core equivalence chain proving Kadane's algorithm correctness:**

### ✅ ALL FORMS PROVEN
- **`form1_eq_form2`** - Simple reflexivity (segs = concat ∘ map inits ∘ tails)
- **`form2_eq_form3`** - Function composition reordering
- **`form3_eq_form4`** - Fold promotion application
- **`form4_eq_form5`** - Map distribution properties
- **`form5_eq_form6`** - Horner's rule transformation
- **`form6_eq_form7`** - Scan-tails relationship
- **`form7_eq_form8`** - Fold-scan fusion

### 🏆 MAIN THEOREM (PROVEN)
- **`MaxSegSum_Equivalence`** - **form1 = form8** (Kadane's correctness)
  - **Status**: Complete with Qed (0 Admitted statements)

---

## 📐 MATHEMATICAL PROPERTIES

**Distributivity, commutativity, and algebraic properties:**

### ✅ PURE MATHEMATICAL LEMMAS
- **`nonNegPlus_comm`** - Commutativity: `nonNegPlus x y = nonNegPlus y x`
- **`nonNegPlus_distributes_over_max`** 🎯 - **Key distributivity property**
- **`nonNegPlus_zero_right`** - Right zero: `nonNegPlus x 0 = max x 0`  
- **`nonNegPlus_zero_left`** - Left zero: `nonNegPlus 0 x = max 0 x`
- **`nonNegPlus_idempotent_zero`** - Zero property: `nonNegPlus 0 0 = 0`
- **`max_idempotent`** - Max idempotency: `max x x = x`
- **`max_add_distributes`** - Addition over max: `max s t + x = max (s + x) (t + x)`

### 🧮 ARITHMETIC UTILITIES  
- **`inits_cons`** - Induction helper: `inits (x :: xs) = [] :: map (cons x) (inits xs)`
- **`app_concat`** - List concatenation: `xs ++ ys = concat [xs; ys]`
- **`fold_left_nil`**, **`fold_right_nil`** - Fold base cases

---

## 📋 LIST OPERATIONS

**Core list manipulation functions and their properties:**

### ✅ TAILS PROPERTIES
- **`tails_nil`** - Empty list: `tails [] = [[]]`
- **`tails_singleton`** - Single element: `tails [x] = [[x]; []]`
- **`tails_one`**, **`tails_two`** - Concrete examples for [1], [1;2]
- **`tails_rec_test1`** - Test case for recursive definition

### ✅ SCAN OPERATIONS
- **`scan_right_tails_rec_fold`** 🎯 - **BREAKTHROUGH**: Core scan-tails relationship
  - **Statement**: `scan_right f i xs = map (fold_right f i) (tails_rec xs)`
  - **Impact**: Enabled pure proof of form6_eq_form7
- **`scan_right_singleton`**, **`scan_right_nil`** - Base cases
- **`scan_right_tails_example_nil/one`** - Concrete examples

### ✅ FUNCTION COMPOSITION
- **`map_promotion`** - Map over composition: `map f ∘ map g = map (f ∘ g)`
- **`fold_promotion`** - Fold distribution: `nonNegMaximum ∘ concat = nonNegMaximum ∘ map nonNegMaximum`
- **`functions_not_equal`** - Counter-example for function equality

---

## 🎓 KEY SUPPORTING THEOREMS

**Major lemmas proven to support the form transformations:**

### 🔬 MATHEMATICAL FOUNDATIONS
1. **`nonneg_tropical_fold_right_returns_max`** (formerly generalised_horners_rule)
   - **Type**: Fold equivalence over inits using tropical operations
   - **Used in**: `form5_eq_form6`
   - **Status**: Proven with Qed

2. **`fold_scan_fusion_pair`** (fold-scan fusion law)
   - **Type**: Relationship between fold and scan operations
   - **Used in**: `form7_eq_form8`
   - **Status**: Proven with Qed

### 🔗 SCAN-TAILS RELATIONSHIP
3. **`scan_right_tails_rec_fold`** - Core scan-tails theorem
   - **Statement**: `scan_right f i xs = map (fold_right f i) (tails_rec xs)`
   - **Used in**: `form6_eq_form7`
   - **Status**: Proven with Qed

---

## 🔍 SEARCH INDEX

**Quick lookup by mathematical concept:**

### By Mathematical Operation
- **Max operations**: `max_idempotent`, `max_add_distributes`, `nonNegPlus_distributes_over_max`
- **Addition/Plus**: `nonNegPlus_comm`, `nonNegPlus_zero_left/right`, `max_add_distributes`
- **Fold operations**: `fold_promotion`, `fold_left_nil`, `fold_right_nil`, `nonneg_tropical_fold_right_returns_max`
- **Scan operations**: `scan_right_tails_rec_fold`, `scan_right_singleton/nil`, `fold_scan_fusion_pair`

### By List Function
- **tails**: `tails_nil`, `tails_singleton`, `scan_right_tails_rec_fold`
- **inits**: `inits_cons`, `nonneg_tropical_fold_right_returns_max`
- **map**: `map_promotion`, `fold_promotion`
- **concat**: `app_concat`, `fold_promotion`

### By Proof Status
- **All proofs complete**: BirdMeertens integer-specific proof has 0 Admitted statements
- **Generalized proof**: See KadanesAlgorithm/ for semiring-based framework
- **Alternative approach**: See TropicalMaxSegSum.v for tropical semiring formulation

---

## 💡 PROOF ARCHITECTURE

### 🎯 Key Proven Theorems
- **`form6_eq_form7`** - Pure proof using tails_rec strategy
- **`nonNegPlus_distributes_over_max`** - Distributivity via case analysis
- **`scan_right_tails_rec_fold`** - Core scan-tails relationship
- **`nonneg_tropical_fold_right_returns_max`** - Horner's rule for tropical operations
- **`fold_scan_fusion_pair`** - Fold-scan fusion law

### 🔑 Reusable Lemmas
- **`inits_cons`** - Induction helper for inits
- **`nonNegPlus_distributes_over_max`** - Distributivity property
- **`map_promotion`**, **`fold_promotion`** - Function composition

### ⚡ Proof Techniques Used
- **Tails recursion strategy**: Enabled pure proofs avoiding fold_right complexity
- **Case analysis**: For distributivity and arithmetic properties
- **Induction**: For scan-tails and Horner's rule theorems
- **Function extensionality**: For form equivalences

---

*This reference catalog documents the BirdMeertens integer-specific proof (complete with 0 Admitted). Use Ctrl+F to search by theorem name, mathematical property, or list operation.*