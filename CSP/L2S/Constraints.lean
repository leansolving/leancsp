import CSP.L2S.Core
import CSP.Core
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort

namespace CSP.L2S

/-!
# L2M Tagged Constraint Implementations

This module provides all tagged constraint constructors with dual representation:
- **Semantic Pattern**: High-level structure for MiniZinc translation
- **Dynamic Checker**: Executable predicate for Lean proofs

## Constraint Categories

1. **Global Constraints**: alldifferent, count, element, min/max
2. **Arithmetic Constraints**: sum with all relational operators
3. **Binary Comparisons**: =, ≠, <, ≤, >, ≥ between variables
4. **Unary Comparisons**: =, ≠, <, ≤, >, ≥ with constants
5. **Bound Constraints**: Variable domain specification
6. **N-Queens Specific**: Diagonal alldifferent constraints

## Adding New Constraints

1. Add pattern to `ConstraintPattern` in Core.lean
2. Create constructor function here
3. Add MiniZinc translation in Translator.lean
-/

open IntCSP
open ConstraintPattern

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Extract values from ScopeValues for integer homogeneous domain -/
def extractValues {num_vars n : ℕ} {scope : _root_.Vector (VarType num_vars) n}
    (values : ScopeValues (VarType num_vars) (fun _ => IntDomain) scope) :
    List IntDomain :=
  List.ofFn fun i => values i

-- ============================================================================
-- Global Constraints
-- ============================================================================

section GlobalConstraints

variable {num_vars : ℕ}

/-- Alldifferent constraint: all variables must have different values -/
def alldifferent {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      decide valueList.Nodup
  }
  { pattern := ConstraintPattern.alldifferent (scope.toList.map (·.val))
    dynamic := DynamicConstraint.mk n checker }

/-- Increasing constraint: variables must be in non-decreasing order.
    Maps to MiniZinc's `increasing` global constraint. -/
def increasing {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      decide (List.Pairwise (· ≤ ·) valueList)
  }
  { pattern := ConstraintPattern.increasing (scope.toList.map (·.val))
    dynamic := DynamicConstraint.mk n checker }

/-- Count constraint: count occurrences of a value -/
def count {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (value : IntDomain) (target : ℕ) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      decide ((valueList.filter (· = value)).length = target)
  }
  { pattern := ConstraintPattern.count (scope.toList.map (·.val)) value target
    dynamic := DynamicConstraint.mk n checker }

/-- Count constraint with variable result: count(vars, value) = count_var
    Used in magic sequence problems where the count must equal another variable. -/
def count_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (value : IntDomain) (count_result : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[count_result], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vars := valueList.take n
      match valueList[n]? with
      | some countVal =>
        let actualCount := (vars.filter (· = value)).length
        decide (actualCount = countVal.natAbs)
      | none => false
  }
  { pattern := ConstraintPattern.count_var (scope.toList.map (·.val)) value count_result.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

/-- Element constraint: array[index] = result -/
def element (index_var result_var : VarType num_vars)
    (array : List IntDomain) :
    TaggedConstraint num_vars :=
  let scope := ⟨#[index_var, result_var], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 2 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [idx, res] =>
        -- MiniZinc arrays use 1-based indexing, Lean lists use 0-based
        -- Index 1 in MiniZinc corresponds to position 0 in Lean list
        if idx ≥ 1 then
          match array[idx.natAbs - 1]? with
          | some elem => decide (elem = res)
          | none => false
        else false
      | _ => false
  }
  { pattern := ConstraintPattern.element index_var.val array result_var.val
    dynamic := DynamicConstraint.mk 2 checker }

/-- Maximum constraint: max(vars) = maxVar -/
def maximum {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (maxVar : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[maxVar], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vals := valueList.dropLast
      match valueList.getLast? with
      | some maxVal => decide (vals.all (· ≤ maxVal) ∧ vals.any (· = maxVal))
      | none => false
  }
  { pattern := ConstraintPattern.maximum (scope.toList.map (·.val)) maxVar.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

/-- Minimum constraint: min(vars) = minVar -/
def minimum {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (minVar : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[minVar], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vals := valueList.dropLast
      match valueList.getLast? with
      | some minVal => decide (vals.all (· ≥ minVal) ∧ vals.any (· = minVal))
      | none => false
  }
  { pattern := ConstraintPattern.minimum (scope.toList.map (·.val)) minVar.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

end GlobalConstraints

-- ============================================================================
-- Arithmetic Constraints
-- ============================================================================

section ArithmeticConstraints

variable {num_vars : ℕ}

/-- General sum constraint with relation operator -/
def sum_rel {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (op : RelOp) (target : ℤ) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      let s := valueList.sum
      match op with
      | .EQ => decide (s = target)
      | .NE => decide (s ≠ target)
      | .LT => decide (s < target)
      | .LE => decide (s ≤ target)
      | .GT => decide (s > target)
      | .GE => decide (s ≥ target)
  }
  { pattern := ConstraintPattern.sum (scope.toList.map (·.val)) op target
    dynamic := DynamicConstraint.mk n checker }

/-- Sum equality constraint: sum of variables equals target -/
def sum_eq {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    TaggedConstraint num_vars :=
  sum_rel scope .EQ target

/-- Sum less-than-or-equal constraint -/
def sum_le {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    TaggedConstraint num_vars :=
  sum_rel scope .LE target

/-- Sum less-than constraint -/
def sum_lt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    TaggedConstraint num_vars :=
  sum_rel scope .LT target

/-- Sum greater-than-or-equal constraint -/
def sum_ge {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    TaggedConstraint num_vars :=
  sum_rel scope .GE target

/-- Sum greater-than constraint -/
def sum_gt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    TaggedConstraint num_vars :=
  sum_rel scope .GT target

/-- Sum not-equal constraint -/
def sum_ne {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    TaggedConstraint num_vars :=
  sum_rel scope .NE target

/-- General linear equation constraint with coefficients: c₀*v₀ + c₁*v₁ + ... op target
    This is a weighted sum (scalar product / dot product) constraint. -/
def linear_rel {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (op : RelOp) (target : ℤ) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      -- Compute the weighted sum (dot product): c₀*v₀ + c₁*v₁ + ...
      let weightedSum := List.zipWith (· * ·) coeffs.toList valueList |>.sum
      match op with
      | .EQ => decide (weightedSum = target)
      | .NE => decide (weightedSum ≠ target)
      | .LT => decide (weightedSum < target)
      | .LE => decide (weightedSum ≤ target)
      | .GT => decide (weightedSum > target)
      | .GE => decide (weightedSum ≥ target)
  }
  { pattern := ConstraintPattern.linear (scope.toList.map (·.val)) coeffs.toList op target
    dynamic := DynamicConstraint.mk n checker }

/-- Linear equality constraint: c₀*v₀ + c₁*v₁ + ... = target -/
def linear_eq {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    TaggedConstraint num_vars :=
  linear_rel scope coeffs .EQ target

/-- Linear less-than-or-equal constraint -/
def linear_le {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    TaggedConstraint num_vars :=
  linear_rel scope coeffs .LE target

/-- Linear less-than constraint -/
def linear_lt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    TaggedConstraint num_vars :=
  linear_rel scope coeffs .LT target

/-- Linear greater-than-or-equal constraint -/
def linear_ge {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    TaggedConstraint num_vars :=
  linear_rel scope coeffs .GE target

/-- Linear greater-than constraint -/
def linear_gt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    TaggedConstraint num_vars :=
  linear_rel scope coeffs .GT target

/-- Linear not-equal constraint -/
def linear_ne {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    TaggedConstraint num_vars :=
  linear_rel scope coeffs .NE target

end ArithmeticConstraints

-- ============================================================================
-- Bound Constraints
-- ============================================================================

section BoundConstraints

/-- Bound constraint: lb ≤ var ≤ ub -/
def bound {num_vars : ℕ} (var : VarType num_vars) (lb ub : ℤ) :
    TaggedConstraint num_vars :=
  let scope := ⟨#[var], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 1 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [val] => decide (lb ≤ val ∧ val ≤ ub)
      | _ => false
  }
  { pattern := ConstraintPattern.bound var.val lb ub
    dynamic := DynamicConstraint.mk 1 checker }

end BoundConstraints

-- ============================================================================
-- Binary Comparison Constraints (Variable to Variable)
-- ============================================================================

section BinaryComparisons

variable {num_vars : ℕ}

/-- Binary equality constraint: v1 = v2 -/
def equal (v1 v2 : VarType num_vars) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.eq v1.val v2.val
  dynamic := binary_dynamic_constraint v1 v2 (fun x y => decide (x = y)) }

/-- Binary not-equal constraint: v1 ≠ v2 -/
def not_equal (v1 v2 : VarType num_vars) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.ne v1.val v2.val
  dynamic := binary_dynamic_constraint v1 v2 (fun x y => decide (x ≠ y)) }

/-- Binary less-than constraint: v1 < v2 -/
def less_than (v1 v2 : VarType num_vars) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.lt v1.val v2.val
  dynamic := binary_dynamic_constraint v1 v2 (fun x y => decide (x < y)) }

/-- Binary less-than-or-equal constraint: v1 ≤ v2 -/
def less_equal (v1 v2 : VarType num_vars) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.le v1.val v2.val
  dynamic := binary_dynamic_constraint v1 v2 (fun x y => decide (x ≤ y)) }

/-- Binary greater-than constraint: v1 > v2 -/
def greater_than (v1 v2 : VarType num_vars) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.gt v1.val v2.val
  dynamic := binary_dynamic_constraint v1 v2 (fun x y => decide (x > y)) }

/-- Binary greater-than-or-equal constraint: v1 ≥ v2 -/
def greater_equal (v1 v2 : VarType num_vars) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.ge v1.val v2.val
  dynamic := binary_dynamic_constraint v1 v2 (fun x y => decide (x ≥ y)) }

end BinaryComparisons

-- ============================================================================
-- Unary Comparison Constraints (Variable to Constant)
-- ============================================================================

section UnaryComparisons

variable {num_vars : ℕ}

/-- Variable equals constant: v = c -/
def equals_const (v : VarType num_vars) (c : ℤ) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.eq_const v.val c
  dynamic := unary_dynamic_constraint v (fun x => decide (x = c)) }

/-- Variable not equal to constant: v ≠ c -/
def not_equals_const (v : VarType num_vars) (c : ℤ) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.ne_const v.val c
  dynamic := unary_dynamic_constraint v (fun x => decide (x ≠ c)) }

/-- Variable less than constant: v < c -/
def less_than_const (v : VarType num_vars) (c : ℤ) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.lt_const v.val c
  dynamic := unary_dynamic_constraint v (fun x => decide (x < c)) }

/-- Variable less than or equal to constant: v ≤ c -/
def less_equal_const (v : VarType num_vars) (c : ℤ) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.le_const v.val c
  dynamic := unary_dynamic_constraint v (fun x => decide (x ≤ c)) }

/-- Variable greater than constant: v > c -/
def greater_than_const (v : VarType num_vars) (c : ℤ) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.gt_const v.val c
  dynamic := unary_dynamic_constraint v (fun x => decide (x > c)) }

/-- Variable greater than or equal to constant: v ≥ c -/
def greater_equal_const (v : VarType num_vars) (c : ℤ) :
    TaggedConstraint num_vars := {
  pattern := ConstraintPattern.ge_const v.val c
  dynamic := unary_dynamic_constraint v (fun x => decide (x ≥ c)) }

end UnaryComparisons

-- ============================================================================
-- N-Queens Specific Constraints
-- ============================================================================

section NQueens

/-- Alldifferent diagonal constraint for N-Queens (positive diagonal): x[i] + i all different -/
def alldifferent_diag_pos (n : ℕ) : TaggedConstraint n :=
  let scope := _root_.Vector.ofFn (fun i : Fin n => i)
  let checker : Constraint (VarType n) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let diagonals := List.ofFn fun (i : Fin n) => (values i) + i.val
      decide diagonals.Nodup
  }
  { pattern := ConstraintPattern.alldifferentOffset
      (List.range n)
      ((List.range n).map Int.ofNat)
    dynamic := DynamicConstraint.mk n checker }

/-- Alldifferent diagonal constraint for N-Queens (negative diagonal): x[i] - i all different -/
def alldifferent_diag_neg (n : ℕ) : TaggedConstraint n :=
  let scope := _root_.Vector.ofFn (fun i : Fin n => i)
  let checker : Constraint (VarType n) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let diagonals := List.ofFn fun (i : Fin n) => (values i) - i.val
      decide diagonals.Nodup
  }
  { pattern := ConstraintPattern.alldifferentOffset
      (List.range n)
      ((List.range n).map fun i => -(Int.ofNat i))
    dynamic := DynamicConstraint.mk n checker }

end NQueens

-- ============================================================================
-- Schur Number Constraints
-- ============================================================================

section SchurConstraints

variable {num_vars : ℕ}

/-- Schur triple constraint: not all three variables have the same value.
    Translates to MiniZinc as: x != y \/ x != z \/ y != z
    Used in Schur number problem to ensure no box contains a sum triple {x,y,z} where x+y=z -/
def schur_triple (v1 v2 v3 : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 := ⟨#[v1, v2, v3], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 3 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y, z] => decide (x ≠ y ∨ x ≠ z ∨ y ≠ z)
      | _ => false
  }
  { pattern := ConstraintPattern.schur_triple v1.val v2.val v3.val
    dynamic := DynamicConstraint.mk 3 checker }

end SchurConstraints

-- ============================================================================
-- Absolute Value Constraints
-- ============================================================================

section AbsoluteValueConstraints

variable {num_vars : ℕ}

/-- Absolute difference constraint: |var1 - var2| op target
    Translates to MiniZinc as: abs(x[var1] - x[var2]) op target
    Used in graph labeling and distance constraints -/
def abs_diff_rel {num_vars : ℕ} (v1 v2 : VarType num_vars) (op : RelOp) (target : ℤ) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 2 := ⟨#[v1, v2], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 2 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y] =>
        let abs_diff := Int.natAbs (x - y)
        match op with
        | RelOp.EQ => decide (abs_diff = target)
        | RelOp.NE => decide (abs_diff ≠ target)
        | RelOp.LT => decide (abs_diff < target)
        | RelOp.LE => decide (abs_diff ≤ target)
        | RelOp.GT => decide (abs_diff > target)
        | RelOp.GE => decide (abs_diff ≥ target)
      | _ => false
  }
  { pattern := ConstraintPattern.abs_diff_rel v1.val v2.val op target
    dynamic := DynamicConstraint.mk 2 checker }

/-- Convenience: |var1 - var2| >= target -/
def abs_diff_ge {num_vars : ℕ} (v1 v2 : VarType num_vars) (target : ℤ) :
    TaggedConstraint num_vars :=
  abs_diff_rel v1 v2 RelOp.GE target

/-- Convenience: |var1 - var2| <= target -/
def abs_diff_le {num_vars : ℕ} (v1 v2 : VarType num_vars) (target : ℤ) :
    TaggedConstraint num_vars :=
  abs_diff_rel v1 v2 RelOp.LE target

/-- Convenience: |var1 - var2| = target -/
def abs_diff_eq {num_vars : ℕ} (v1 v2 : VarType num_vars) (target : ℤ) :
    TaggedConstraint num_vars :=
  abs_diff_rel v1 v2 RelOp.EQ target

/-- Absolute difference to variable: result = |var1 - var2|
    Translates to MiniZinc as: x[result] = abs(x[var1] - x[var2])
    Used when the absolute difference must be stored in a variable -/
def abs_diff_var {num_vars : ℕ} (v1 v2 result : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 := ⟨#[v1, v2, result], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 3 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y, diff] => decide (diff = Int.natAbs (x - y))
      | _ => false
  }
  { pattern := ConstraintPattern.abs_diff_var v1.val v2.val result.val
    dynamic := DynamicConstraint.mk 3 checker }

end AbsoluteValueConstraints

-- ============================================================================
-- Modulo Constraints
-- ============================================================================

section ModuloConstraints

variable {num_vars : ℕ}

/-- Modulo constraint: var mod n = k
    Translates to MiniZinc as: x[var] mod n = k
    Used in problems with cyclic/periodic conditions -/
def modulo {num_vars : ℕ} (v : VarType num_vars) (n k : ℤ) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 1 := ⟨#[v], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 1 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x] => decide (x % n = k)
      | _ => false
  }
  { pattern := ConstraintPattern.modulo v.val n k
    dynamic := DynamicConstraint.mk 1 checker }

end ModuloConstraints

-- ============================================================================
-- Sliding Window Constraints
-- ============================================================================

section SlidingWindowConstraints

variable {num_vars : ℕ}

/-- Sliding sum constraint: for each consecutive window of size `window_size`,
    the sum of values in that window satisfies `op target`.

    For Car Sequencing: ensures that in any consecutive sequence of `b` cars,
    at most `m` have a particular feature (when op = LE, target = m).

    Translates to MiniZinc's `sliding_sum` global constraint. -/
def sliding_sum {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (window_size : ℕ) (op : RelOp) (target : ℤ) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      -- Check all possible windows of the specified size
      let allWindowsValid := List.range (n - window_size + 1) |>.all fun start_pos =>
        let window := valueList.drop start_pos |>.take window_size
        let window_sum := window.sum
        match op with
        | .EQ => window_sum = target
        | .NE => window_sum ≠ target
        | .LT => window_sum < target
        | .LE => window_sum ≤ target
        | .GT => window_sum > target
        | .GE => window_sum ≥ target
      decide allWindowsValid
  }
  { pattern := ConstraintPattern.sliding_sum (scope.toList.map (·.val)) window_size op target
    dynamic := DynamicConstraint.mk n checker }

/-- Convenience: sliding sum ≤ target (most common for Car Sequencing) -/
def sliding_sum_le {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (window_size : ℕ) (target : ℤ) :
    TaggedConstraint num_vars :=
  sliding_sum scope window_size .LE target

/-- Convenience: sliding sum = target -/
def sliding_sum_eq {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (window_size : ℕ) (target : ℤ) :
    TaggedConstraint num_vars :=
  sliding_sum scope window_size .EQ target

end SlidingWindowConstraints

-- ============================================================================
-- Boolean Gate Constraints
-- ============================================================================

section BooleanGates

variable {num_vars : ℕ}

/-- NOT gate constraint: out = ¬in
    For 0/1 variables: out = 1 - in
    Equivalently: out + in = 1 -/
def not_gate {num_vars : ℕ} (in1 out : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 2 := ⟨#[in1, out], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 2 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, z] =>
        -- out = 1 - in (for Boolean 0/1 variables)
        decide (z = 1 - x)
      | _ => false
  }
  { pattern := ConstraintPattern.not_gate in1.val out.val
    dynamic := DynamicConstraint.mk 2 checker }

/-- AND gate constraint: out = in1 ∧ in2
    For 0/1 variables, this ensures out=1 iff both inputs are 1.
    Semantically: out = min(in1, in2) -/
def and_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 := ⟨#[in1, in2, out], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 3 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y, z] =>
        -- out = min(in1, in2)
        decide (z = min x y)
      | _ => false
  }
  { pattern := ConstraintPattern.and_gate in1.val in2.val out.val
    dynamic := DynamicConstraint.mk 3 checker }

/-- OR gate constraint: out = in1 ∨ in2
    For 0/1 variables, this ensures out=1 iff at least one input is 1.
    Semantically: out = max(in1, in2) -/
def or_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 := ⟨#[in1, in2, out], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 3 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y, z] =>
        -- out = max(in1, in2)
        decide (z = max x y)
      | _ => false
  }
  { pattern := ConstraintPattern.or_gate in1.val in2.val out.val
    dynamic := DynamicConstraint.mk 3 checker }

/-- XOR gate constraint: out = in1 ⊕ in2
    For 0/1 variables: out = (in1 + in2) mod 2
    Equivalent to: out = in1 + in2 - 2*(in1 AND in2)

    For integer checking, we verify: out = 1 iff exactly one input is 1. -/
def xor_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 := ⟨#[in1, in2, out], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 3 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y, z] =>
        -- Modulo-2 encoding (matches MiniZinc)
        -- (in1 + in2) mod 2 = out
        decide ((x + y) % 2 = z)
      | _ => false
  }
  { pattern := ConstraintPattern.xor_gate in1.val in2.val out.val
    dynamic := DynamicConstraint.mk 3 checker }

/-- NAND gate constraint: out = ¬(in1 ∧ in2)
    For 0/1 variables: out = 1 - (in1 AND in2)
    Equivalent to: out = 0 iff both inputs are 1. -/
def nand_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 := ⟨#[in1, in2, out], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 3 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y, z] =>
        -- NAND = NOT(AND): out = 1 - (in1 AND in2)
        -- Equivalently: out ≥ 1 - in1, out ≥ 1 - in2, out ≤ 2 - in1 - in2
        decide (z ≥ 1 - x ∧ z ≥ 1 - y ∧ z ≤ 2 - x - y)
      | _ => false
  }
  { pattern := ConstraintPattern.nand_gate in1.val in2.val out.val
    dynamic := DynamicConstraint.mk 3 checker }

/-- NOR gate constraint: out = ¬(in1 ∨ in2)
    For 0/1 variables: out = 1 - (in1 OR in2)
    Equivalent to: out = 1 iff both inputs are 0. -/
def nor_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 := ⟨#[in1, in2, out], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 3 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y, z] =>
        -- NOR = NOT(OR): out = 1 - (in1 OR in2)
        -- Equivalently: out ≤ 1 - in1, out ≤ 1 - in2, out ≥ 1 - in1 - in2
        decide (z ≤ 1 - x ∧ z ≤ 1 - y ∧ z ≥ 1 - x - y)
      | _ => false
  }
  { pattern := ConstraintPattern.nor_gate in1.val in2.val out.val
    dynamic := DynamicConstraint.mk 3 checker }

end BooleanGates

-- ============================================================================
-- Multi-Input Logical Operations
-- ============================================================================

section MultiInputLogic

variable {num_vars : ℕ}

/-- AND-all constraint: result = ∧ vars
    Result is 1 iff all variables in vars are 1.
    Semantically: result = min(vars) -/
def and_all {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (result : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[result], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vars := valueList.dropLast
      match valueList.getLast? with
      | some r =>
        -- result = min(vars): r = 1 iff all vars are 1 (for 0/1 values)
        if vars.isEmpty then false
        else
          let minVal := vars.foldl (fun acc x => if x < acc then x else acc) (vars.head!)
          decide (r = minVal)
      | none => false
  }
  { pattern := ConstraintPattern.and_all (scope.toList.map (·.val)) result.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

/-- OR-all constraint: result = ∨ vars
    Result is 1 iff at least one variable in vars is 1. -/
def or_all {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (result : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[result], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vars := valueList.dropLast
      match valueList.getLast? with
      | some r =>
        -- OR-all: r = max(vars)
        -- For 0/1 values, this is equivalent to: r = 1 iff at least one var is 1
        if vars.isEmpty then false
        else
          let maxVal := vars.foldl (fun acc x => if x > acc then x else acc) (vars.head!)
          decide (r = maxVal)
      | none => false
  }
  { pattern := ConstraintPattern.or_all (scope.toList.map (·.val)) result.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

/-- XOR-all constraint: result = ⊕ vars (n-ary XOR / parity)
    Result is 1 iff an odd number of variables in vars are 1.
    This is the parity function used in ECC and cryptography. -/
def xor_all {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (result : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[result], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vars := valueList.dropLast
      match valueList.getLast? with
      | some r =>
        -- r = (sum of vars) mod 2 (parity)
        decide (vars.sum % 2 = r)
      | none => false
  }
  { pattern := ConstraintPattern.xor_all (scope.toList.map (·.val)) result.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

end MultiInputLogic

-- ============================================================================
-- Implication and Equivalence Constraints
-- ============================================================================

section ImplicationConstraints

variable {num_vars : ℕ}

/-- Implication constraint: premise ⇒ conclusion
    For 0/1 variables: if premise=1 then conclusion=1.
    Encodes as: conclusion ≥ premise -/
def implies {num_vars : ℕ} (premise conclusion : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 2 := ⟨#[premise, conclusion], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 2 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [p, q] =>
        -- Arithmetic encoding (matches MiniZinc): conclusion ≥ premise
        -- For 0/1 variables, this is equivalent to: premise → conclusion
        decide (q ≥ p)
      | _ => false
  }
  { pattern := ConstraintPattern.implies premise.val conclusion.val
    dynamic := DynamicConstraint.mk 2 checker }

/-- If-and-only-if constraint: var1 ↔ var2
    For 0/1 variables: var1 and var2 must have the same value.
    Encodes as: var1 = var2 -/
def iff {num_vars : ℕ} (var1 var2 : VarType num_vars) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 2 := ⟨#[var1, var2], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 2 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [x, y] =>
        -- Arithmetic encoding (matches MiniZinc): var1 = var2
        -- For 0/1 variables, this is equivalent to: var1 ↔ var2
        decide (x = y)
      | _ => false
  }
  { pattern := ConstraintPattern.iff var1.val var2.val
    dynamic := DynamicConstraint.mk 2 checker }

/-- If-then constraint: if var = value then next_var = next_value.
    Reified implication for state transitions: (var = value) → (next_var = next_value) -/
def if_then {num_vars : ℕ}
    (var : VarType num_vars) (value : ℤ)
    (next_var : VarType num_vars) (next_value : ℤ) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 2 := ⟨#[var, next_var], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 2 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [v, nv] =>
        -- If v = value, then nv must equal next_value
        -- Otherwise, no constraint on nv
        decide (v ≠ value ∨ nv = next_value)
      | _ => false
  }
  { pattern := ConstraintPattern.if_then var.val value next_var.val next_value
    dynamic := DynamicConstraint.mk 2 checker }

/-- If-then-or constraint: if var = value then next_var ∈ allowed_values.
    Disjunctive implication for non-deterministic state transitions:
    (var = value) → (next_var ∈ allowed_values) -/
def if_then_or {num_vars : ℕ}
    (var : VarType num_vars) (value : ℤ)
    (next_var : VarType num_vars) (allowed_values : List ℤ) :
    TaggedConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 2 := ⟨#[var, next_var], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) 2 := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      match valueList with
      | [v, nv] =>
        -- If v = value, then nv must be in allowed_values
        -- Otherwise, no constraint on nv
        decide (v ≠ value ∨ allowed_values.contains nv)
      | _ => false
  }
  { pattern := ConstraintPattern.if_then_or var.val value next_var.val allowed_values
    dynamic := DynamicConstraint.mk 2 checker }

end ImplicationConstraints

-- ============================================================================
-- Cardinality Constraints
-- ============================================================================

section CardinalityConstraints

variable {num_vars : ℕ}

/-- At-least-k constraint: at least k variables must be 1.
    For 0/1 variables: sum(vars) ≥ k -/
def at_least_k {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (k : ℕ) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      decide (valueList.sum ≥ k)
  }
  { pattern := ConstraintPattern.at_least_k (scope.toList.map (·.val)) k
    dynamic := DynamicConstraint.mk n checker }

/-- At-most-k constraint: at most k variables can be 1.
    For 0/1 variables: sum(vars) ≤ k -/
def at_most_k {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (k : ℕ) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      decide (valueList.sum ≤ k)
  }
  { pattern := ConstraintPattern.at_most_k (scope.toList.map (·.val)) k
    dynamic := DynamicConstraint.mk n checker }

/-- Exactly-k constraint: exactly k variables must be 1.
    For 0/1 variables: sum(vars) = k -/
def exactly_k {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (k : ℕ) :
    TaggedConstraint num_vars :=
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) n := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      decide (valueList.sum = k)
  }
  { pattern := ConstraintPattern.exactly_k (scope.toList.map (·.val)) k
    dynamic := DynamicConstraint.mk n checker }

end CardinalityConstraints

-- ============================================================================
-- Arithmetic Constraints with Variable Targets
-- ============================================================================

section VariableTargetConstraints

variable {num_vars : ℕ}

/-- Product constraint with variable target: product(vars) op target_var
    Computes the product of all variables in the scope and compares with target variable. -/
def product_rel_var {n : ℕ}
    (scope : _root_.Vector (VarType num_vars) n)
    (op : RelOp)
    (target : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[target], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vars := valueList.dropLast
      match valueList.getLast? with
      | some t =>
        let product := vars.foldl (· * ·) 1
        match op with
        | .EQ => decide (product = t)
        | .NE => decide (product ≠ t)
        | .LT => decide (product < t)
        | .LE => decide (product ≤ t)
        | .GT => decide (product > t)
        | .GE => decide (product ≥ t)
      | none => false
  }
  { pattern := ConstraintPattern.product_rel_var (scope.toList.map (·.val)) op target.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

/-- Linear constraint with variable target: Σ(coeffs[i] * vars[i]) op target_var -/
def linear_rel_var {n : ℕ}
    (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n)
    (op : RelOp)
    (target : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[target], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vars := valueList.dropLast
      match valueList.getLast? with
      | some t =>
        let weightedSum := List.zipWith (· * ·) coeffs.toList vars |>.sum
        match op with
        | .EQ => decide (weightedSum = t)
        | .NE => decide (weightedSum ≠ t)
        | .LT => decide (weightedSum < t)
        | .LE => decide (weightedSum ≤ t)
        | .GT => decide (weightedSum > t)
        | .GE => decide (weightedSum ≥ t)
      | none => false
  }
  { pattern := ConstraintPattern.linear_rel_var (scope.toList.map (·.val)) coeffs.toList op target.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

/-- Sum constraint with variable target: sum(vars) op target_var -/
def sum_rel_var {n : ℕ}
    (scope : _root_.Vector (VarType num_vars) n)
    (op : RelOp)
    (target : VarType num_vars) :
    TaggedConstraint num_vars :=
  let fullScope := _root_.Vector.append scope ⟨#[target], rfl⟩
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) (n + 1) := {
    scope := fullScope
    check := fun values =>
      let valueList := extractValues values
      let vars := valueList.dropLast
      match valueList.getLast? with
      | some t =>
        let s := vars.sum
        match op with
        | .EQ => decide (s = t)
        | .NE => decide (s ≠ t)
        | .LT => decide (s < t)
        | .LE => decide (s ≤ t)
        | .GT => decide (s > t)
        | .GE => decide (s ≥ t)
      | none => false
  }
  { pattern := ConstraintPattern.sum_rel_var (scope.toList.map (·.val)) op target.val
    dynamic := DynamicConstraint.mk (n + 1) checker }

/-- Convenient aliases for common cases -/
def product_eq_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : TaggedConstraint num_vars :=
  product_rel_var scope .EQ target

def product_ne_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : TaggedConstraint num_vars :=
  product_rel_var scope .NE target

def linear_eq_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : VarType num_vars) : TaggedConstraint num_vars :=
  linear_rel_var scope coeffs .EQ target

def linear_ne_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : VarType num_vars) : TaggedConstraint num_vars :=
  linear_rel_var scope coeffs .NE target

def sum_eq_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : TaggedConstraint num_vars :=
  sum_rel_var scope .EQ target

def sum_ne_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : TaggedConstraint num_vars :=
  sum_rel_var scope .NE target

end VariableTargetConstraints

-- ============================================================================
-- Scheduling Constraints
-- ============================================================================

section SchedulingConstraints

/-- Disjunctive constraint: tasks on a unary resource must not overlap.
    For all pairs (i,j): (start[i] + duration[i] ≤ start[j]) ∨ (start[j] + duration[j] ≤ start[i])
    Used for machine mutex in job-shop scheduling. -/
def disjunctive {num_vars : ℕ}
    (tasks : List (VarType num_vars))
    (durations : List ℤ) :
    TaggedConstraint num_vars :=
  -- Scope includes all task variables
  let scope := _root_.Vector.ofFn (fun i : Fin tasks.length => tasks.get ⟨i.val, by omega⟩)
  let checker : Constraint (VarType num_vars) (fun _ => IntDomain) tasks.length := {
    scope := scope
    check := fun values =>
      let valueList := extractValues values
      -- Check all pairs (i,j) where i < j
      let pairs := (List.finRange tasks.length).flatMap fun i =>
        (List.finRange tasks.length).filterMap fun j =>
          if i.val < j.val then some (i, j) else none
      List.all pairs fun (i, j) =>
        let si := valueList[i.val]!
        let sj := valueList[j.val]!
        let di := durations[i.val]!
        let dj := durations[j.val]!
        -- Either task i finishes before task j starts, or vice versa
        decide (si + di ≤ sj ∨ sj + dj ≤ si)
  }
  { pattern := ConstraintPattern.disjunctive (tasks.map (·.val)) durations
    dynamic := DynamicConstraint.mk tasks.length checker }

end SchedulingConstraints

-- ============================================================================
-- Convenience Functions
-- ============================================================================

section Convenience

/-- Create alldifferent constraint for all variables -/
def alldifferent_all (num_vars : ℕ) : TaggedConstraint num_vars :=
  alldifferent (_root_.Vector.ofFn id)

/-- Create sum constraint for all variables -/
def sum_all_eq (num_vars : ℕ) (target : ℤ) : TaggedConstraint num_vars :=
  sum_eq (_root_.Vector.ofFn id) target

end Convenience

end CSP.L2S
