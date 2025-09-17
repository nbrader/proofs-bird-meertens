# BIRDMEERTENS THEOREM REFERENCE CATALOG

**Purpose**: Quick searchable reference for all theorems and lemmas  
**Usage**: Search by theorem name, mathematical property, or list operation  

---

## 📊 PROJECT GOAL

**Objective**: Complete all admitted proofs to achieve full verification of Kadane's algorithm correctness through the Bird-Meertens transformation chain.

**Recent Progress**: Strategic breakthrough using `tails_rec` approach enabled completion of `form6_eq_form7`.

---

## 🎯 FORM TRANSFORMATIONS (Bird-Meertens Algorithm Chain)

**Core equivalence chain proving Kadane's algorithm correctness:**

### ✅ COMPLETED
- **`form1_eq_form2`** - Simple reflexivity (segs = concat ∘ map inits ∘ tails)
- **`form2_eq_form3`** - Function composition reordering 
- **`form3_eq_form4`** - Fold promotion application
- **`form4_eq_form5`** - Map distribution properties
- **`form6_eq_form7`** 🎯 - **PURE PROOF** using tails_rec strategy (scan_right relationship)

### 🚫 ADMITTED (Remaining Work)
- **`form5_eq_form6`** - Requires `generalised_horners_rule`
- **`form7_eq_form8`** - Requires `fold_scan_fusion`

### 🏆 MAIN THEOREM
- **`MaxSegSum_Equivalence`** - **form1 = form8** (Kadane's correctness)
  - **Goal**: Complete all admitted proofs to achieve full verification

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

## 🚫 ADMITTED THEOREMS (Critical Blockers)

**These 3 theorems are the only remaining blockers:**

### 🔬 MATHEMATICAL FOUNDATIONS
1. **`generalised_horners_rule`** ⭐ **LEAF DEPENDENCY**
   - **Type**: Complex mathematical theorem about fold equivalences over inits
   - **Blocks**: `form5_eq_form6`
   - **Complexity**: Very high - requires deep inductive reasoning

2. **`fold_scan_fusion`** ⭐ **LEAF DEPENDENCY**  
   - **Type**: Advanced scan-fold algebraic relationship
   - **Blocks**: `form7_eq_form8`
   - **Complexity**: High - sophisticated algebraic proof

### 🔗 STRUCTURAL (Optional)
3. **`tails_rec_equiv`** - Equivalence: `tails xs = tails_rec xs`
   - **Status**: No longer needed due to strategic refactoring!
   - **Note**: Could be proven for completeness but not required

---

## 🔍 SEARCH INDEX

**Quick lookup by mathematical concept:**

### By Mathematical Operation
- **Max operations**: `max_idempotent`, `max_add_distributes`, `nonNegPlus_distributes_over_max`
- **Addition/Plus**: `nonNegPlus_comm`, `nonNegPlus_zero_left/right`, `max_add_distributes`
- **Fold operations**: `fold_promotion`, `fold_left_nil`, `fold_right_nil`, `generalised_horners_rule`
- **Scan operations**: `scan_right_tails_rec_fold`, `scan_right_singleton/nil`

### By List Function  
- **tails**: `tails_nil`, `tails_singleton`, `tails_rec_equiv`, `scan_right_tails_rec_fold`
- **inits**: `inits_cons`, `generalised_horners_rule` 
- **map**: `map_promotion`, `fold_promotion`
- **concat**: `app_concat`, `fold_promotion`

### By Proof Technique
- **Pure proofs**: Most lemmas in Lemmas.v, form1-4 transformations, form6_eq_form7
- **Inductive proofs**: `scan_right_tails_rec_fold`, `inits_cons`
- **Reflexivity**: `form1_eq_form2`
- **Function extensionality**: `form6_eq_form7`, form transformations

---

## 💡 STRATEGIC INSIGHTS FOR PROOF DEVELOPMENT

### 🎯 Recently Proven (High Value)
- **`form6_eq_form7`** - Now pure, demonstrates tails_rec strategy
- **`nonNegPlus_distributes_over_max`** - Complex case analysis completed
- **`scan_right_tails_rec_fold`** - Core relationship proven via induction

### 🔑 Key Utilities Available
- **`inits_cons`** - Essential for induction on inits
- **`nonNegPlus_distributes_over_max`** - Distributivity when needed
- **`map_promotion`**, **`fold_promotion`** - Function composition properties

### ⚡ Strategic Approach
- **Focus on leaf dependencies**: `generalised_horners_rule`, `fold_scan_fusion`
- **Use tails_rec strategy**: Prefer recursive definitions over complex fold_right equivalences  
- **Leverage pure proofs**: Build on the 26 completed theorems as foundations

---

*This reference catalog contains all proven theorems as of the tails_rec breakthrough. Use Ctrl+F to search by theorem name, mathematical property, or list operation.*