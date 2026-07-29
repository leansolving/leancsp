import CSP.L2S.Core
import CSP.Core
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort

namespace CSP.L2S

/-!
# L2S constraint constructors

One smart constructor per supported constraint, each pairing a semantic pattern (used
by the backends) with an executable checker (used in proofs).  Covers globals
(`alldifferent`, `count`, `element`, min/max), linear arithmetic, binary and unary
comparisons, cardinality, Boolean gates and bounds.

To add a constraint: extend `IntConstraint` in `Core.lean`, add a constructor here,
then add its translation in `Backends/MiniZinc.lean` and `Backends/SMTLIB.lean`.
-/

open IntCSP
open IntConstraint

/-! ### Helper Functions -/

/-- Extract values from ScopeValues for integer homogeneous domain -/
def extractValues {num_vars n : ℕ} {scope : _root_.Vector (VarType num_vars) n}
    (values : ScopeValues (VarType num_vars) (fun _ => IntDomain) scope) :
    List IntDomain :=
  List.ofFn fun i => values i

/-! ### Global Constraints -/

section GlobalConstraints

variable {num_vars : ℕ}

/-- Alldifferent constraint: all variables must have different values -/
def alldifferent {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) :
    IntConstraint num_vars :=
  IntConstraint.alldifferent (scope.toList.map (·.val))

/-- Increasing constraint: variables must be in non-decreasing order.
    Maps to MiniZinc's `increasing` global constraint. -/
def increasing {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) :
    IntConstraint num_vars :=
  IntConstraint.increasing (scope.toList.map (·.val))

/-- Count constraint: count occurrences of a value -/
def count {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (value : IntDomain) (target : ℕ) :
    IntConstraint num_vars :=
  IntConstraint.count (scope.toList.map (·.val)) value target

/-- Count constraint with variable result: count(vars, value) = count_var
    Used in magic sequence problems where the count must equal another variable. -/
def count_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (value : IntDomain) (count_result : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.count_var (scope.toList.map (·.val)) value count_result.val

/-- Element constraint: array[index] = result -/
def element (index_var result_var : VarType num_vars)
    (array : List IntDomain) :
    IntConstraint num_vars :=
  IntConstraint.element index_var.val array result_var.val

/-- Maximum constraint: max(vars) = maxVar -/
def maximum {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (maxVar : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.maximum (scope.toList.map (·.val)) maxVar.val

/-- Minimum constraint: min(vars) = minVar -/
def minimum {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (minVar : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.minimum (scope.toList.map (·.val)) minVar.val

/-- Value precedence over `x₀ … x_{num_vars-1}` with `colors` interchangeable colours:
    a colour `v ∈ [1, colors)` may first appear only after `v-1` has (Law–Lee 2004).
    Sound for any CSP closed under colour permutations; the PB backend encodes its
    staircase consequence `xⱼ ≤ j`. -/
def value_precedence (colors : ℕ) : IntConstraint num_vars :=
  IntConstraint.value_precedence colors

/-- Strict lexicographic reversal leader `x <_lex rev(x)` over all variables, for the
    index map `i ↦ (num_vars-1)-i`.  Sound only when that reversal is a symmetry of the
    CSP — see `Proofs/SchurReversalCounterexample.lean`. -/
def strictLexRevLeader : IntConstraint num_vars :=
  IntConstraint.strictLexRevLeader

end GlobalConstraints

/-! ### Arithmetic Constraints -/

section ArithmeticConstraints

variable {num_vars : ℕ}

/-- General sum constraint with relation operator -/
def sum_rel {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (op : RelOp) (target : ℤ) :
    IntConstraint num_vars :=
  IntConstraint.sum (scope.toList.map (·.val)) op target

/-- Sum equality constraint: sum of variables equals target -/
def sum_eq {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    IntConstraint num_vars :=
  sum_rel scope .EQ target

/-- Sum less-than-or-equal constraint -/
def sum_le {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    IntConstraint num_vars :=
  sum_rel scope .LE target

/-- Sum less-than constraint -/
def sum_lt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    IntConstraint num_vars :=
  sum_rel scope .LT target

/-- Sum greater-than-or-equal constraint -/
def sum_ge {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    IntConstraint num_vars :=
  sum_rel scope .GE target

/-- Sum greater-than constraint -/
def sum_gt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    IntConstraint num_vars :=
  sum_rel scope .GT target

/-- Sum not-equal constraint -/
def sum_ne {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (target : ℤ) :
    IntConstraint num_vars :=
  sum_rel scope .NE target

/-- General linear equation constraint with coefficients: c₀*v₀ + c₁*v₁ + ... op target
    This is a weighted sum (scalar product / dot product) constraint. -/
def linear_rel {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (op : RelOp) (target : ℤ) :
    IntConstraint num_vars :=
  IntConstraint.linear (scope.toList.map (·.val)) coeffs.toList op target

/-- Linear equality constraint: c₀*v₀ + c₁*v₁ + ... = target -/
def linear_eq {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    IntConstraint num_vars :=
  linear_rel scope coeffs .EQ target

/-- Linear less-than-or-equal constraint -/
def linear_le {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    IntConstraint num_vars :=
  linear_rel scope coeffs .LE target

/-- Linear less-than constraint -/
def linear_lt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    IntConstraint num_vars :=
  linear_rel scope coeffs .LT target

/-- Linear greater-than-or-equal constraint -/
def linear_ge {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    IntConstraint num_vars :=
  linear_rel scope coeffs .GE target

/-- Linear greater-than constraint -/
def linear_gt {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    IntConstraint num_vars :=
  linear_rel scope coeffs .GT target

/-- Linear not-equal constraint -/
def linear_ne {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : ℤ) :
    IntConstraint num_vars :=
  linear_rel scope coeffs .NE target

end ArithmeticConstraints

/-! ### Bound Constraints -/

section BoundConstraints

/-- Bound constraint: lb ≤ var ≤ ub -/
def bound {num_vars : ℕ} (var : VarType num_vars) (lb ub : ℤ) :
    IntConstraint num_vars :=
  IntConstraint.bound var.val lb ub

end BoundConstraints

/-! ### Binary Comparison Constraints (Variable to Variable) -/

section BinaryComparisons

variable {num_vars : ℕ}

/-- Binary equality constraint: v1 = v2 -/
def equal (v1 v2 : VarType num_vars) :
    IntConstraint num_vars := IntConstraint.eq v1.val v2.val

/-- Binary not-equal constraint: v1 ≠ v2 -/
def not_equal (v1 v2 : VarType num_vars) :
    IntConstraint num_vars := IntConstraint.ne v1.val v2.val

/-- Binary less-than constraint: v1 < v2 -/
def less_than (v1 v2 : VarType num_vars) :
    IntConstraint num_vars := IntConstraint.lt v1.val v2.val

/-- Binary less-than-or-equal constraint: v1 ≤ v2 -/
def less_equal (v1 v2 : VarType num_vars) :
    IntConstraint num_vars := IntConstraint.le v1.val v2.val

/-- Binary greater-than constraint: v1 > v2 -/
def greater_than (v1 v2 : VarType num_vars) :
    IntConstraint num_vars := IntConstraint.gt v1.val v2.val

/-- Binary greater-than-or-equal constraint: v1 ≥ v2 -/
def greater_equal (v1 v2 : VarType num_vars) :
    IntConstraint num_vars := IntConstraint.ge v1.val v2.val

end BinaryComparisons

/-! ### Unary Comparison Constraints (Variable to Constant) -/

section UnaryComparisons

variable {num_vars : ℕ}

/-- Variable equals constant: v = c -/
def equals_const (v : VarType num_vars) (c : ℤ) :
    IntConstraint num_vars := IntConstraint.eq_const v.val c

/-- Variable not equal to constant: v ≠ c -/
def not_equals_const (v : VarType num_vars) (c : ℤ) :
    IntConstraint num_vars := IntConstraint.ne_const v.val c

/-- Variable less than constant: v < c -/
def less_than_const (v : VarType num_vars) (c : ℤ) :
    IntConstraint num_vars := IntConstraint.lt_const v.val c

/-- Variable less than or equal to constant: v ≤ c -/
def less_equal_const (v : VarType num_vars) (c : ℤ) :
    IntConstraint num_vars := IntConstraint.le_const v.val c

/-- Variable greater than constant: v > c -/
def greater_than_const (v : VarType num_vars) (c : ℤ) :
    IntConstraint num_vars := IntConstraint.gt_const v.val c

/-- Variable greater than or equal to constant: v ≥ c -/
def greater_equal_const (v : VarType num_vars) (c : ℤ) :
    IntConstraint num_vars := IntConstraint.ge_const v.val c

end UnaryComparisons

/-! ### N-Queens Specific Constraints -/

section NQueens

/-- Alldifferent diagonal constraint for N-Queens (positive diagonal): x[i] + i all different -/
def alldifferent_diag_pos (n : ℕ) : IntConstraint n :=
  IntConstraint.alldifferentOffset
      (List.range n)
      ((List.range n).map Int.ofNat)

/-- Alldifferent diagonal constraint for N-Queens (negative diagonal): x[i] - i all different -/
def alldifferent_diag_neg (n : ℕ) : IntConstraint n :=
  IntConstraint.alldifferentOffset
      (List.range n)
      ((List.range n).map fun i => -(Int.ofNat i))

end NQueens

/-! ### Schur Number Constraints -/

section SchurConstraints

variable {num_vars : ℕ}

/-- Schur triple constraint: not all three variables have the same value.
    Translates to MiniZinc as: x != y \/ x != z \/ y != z
    Used in Schur number problem to ensure no box contains a sum triple {x,y,z} where x+y=z -/
def schur_triple (v1 v2 v3 : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.schur_triple v1.val v2.val v3.val

end SchurConstraints

/-! ### Absolute Value Constraints -/

section AbsoluteValueConstraints

variable {num_vars : ℕ}

/-- Absolute difference constraint: |var1 - var2| op target
    Translates to MiniZinc as: abs(x[var1] - x[var2]) op target
    Used in graph labeling and distance constraints -/
def abs_diff_rel {num_vars : ℕ} (v1 v2 : VarType num_vars) (op : RelOp) (target : ℤ) :
    IntConstraint num_vars :=
  IntConstraint.abs_diff_rel v1.val v2.val op target

/-- Convenience: |var1 - var2| >= target -/
def abs_diff_ge {num_vars : ℕ} (v1 v2 : VarType num_vars) (target : ℤ) :
    IntConstraint num_vars :=
  abs_diff_rel v1 v2 RelOp.GE target

/-- Convenience: |var1 - var2| <= target -/
def abs_diff_le {num_vars : ℕ} (v1 v2 : VarType num_vars) (target : ℤ) :
    IntConstraint num_vars :=
  abs_diff_rel v1 v2 RelOp.LE target

/-- Convenience: |var1 - var2| = target -/
def abs_diff_eq {num_vars : ℕ} (v1 v2 : VarType num_vars) (target : ℤ) :
    IntConstraint num_vars :=
  abs_diff_rel v1 v2 RelOp.EQ target

/-- Absolute difference to variable: result = |var1 - var2|
    Translates to MiniZinc as: x[result] = abs(x[var1] - x[var2])
    Used when the absolute difference must be stored in a variable -/
def abs_diff_var {num_vars : ℕ} (v1 v2 result : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.abs_diff_var v1.val v2.val result.val

end AbsoluteValueConstraints

/-! ### Modulo Constraints -/

section ModuloConstraints

variable {num_vars : ℕ}

/-- Modulo constraint: var mod n = k
    Translates to MiniZinc as: x[var] mod n = k
    Used in problems with cyclic/periodic conditions -/
def modulo {num_vars : ℕ} (v : VarType num_vars) (n k : ℤ) :
    IntConstraint num_vars :=
  IntConstraint.modulo v.val n k

end ModuloConstraints

/-! ### Sliding Window Constraints -/

section SlidingWindowConstraints

variable {num_vars : ℕ}

/-- Sliding sum: for each consecutive window of size `window_size`, the sum of values
    in that window satisfies `op target`.  Translates to MiniZinc's `sliding_sum`. -/
def sliding_sum {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (window_size : ℕ) (op : RelOp) (target : ℤ) :
    IntConstraint num_vars :=
  IntConstraint.sliding_sum (scope.toList.map (·.val)) window_size op target

/-- Convenience: sliding sum ≤ target (most common for Car Sequencing) -/
def sliding_sum_le {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (window_size : ℕ) (target : ℤ) :
    IntConstraint num_vars :=
  sliding_sum scope window_size .LE target

/-- Convenience: sliding sum = target -/
def sliding_sum_eq {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (window_size : ℕ) (target : ℤ) :
    IntConstraint num_vars :=
  sliding_sum scope window_size .EQ target

end SlidingWindowConstraints

/-! ### Boolean Gate Constraints -/

section BooleanGates

variable {num_vars : ℕ}

/-- NOT gate constraint: out = ¬in
    For 0/1 variables: out = 1 - in
    Equivalently: out + in = 1 -/
def not_gate {num_vars : ℕ} (in1 out : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.not_gate in1.val out.val

/-- AND gate constraint: out = in1 ∧ in2
    For 0/1 variables, this ensures out=1 iff both inputs are 1.
    Semantically: out = min(in1, in2) -/
def and_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.and_gate in1.val in2.val out.val

/-- OR gate constraint: out = in1 ∨ in2
    For 0/1 variables, this ensures out=1 iff at least one input is 1.
    Semantically: out = max(in1, in2) -/
def or_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.or_gate in1.val in2.val out.val

/-- XOR gate constraint: out = in1 ⊕ in2
    For 0/1 variables: out = (in1 + in2) mod 2
    Equivalent to: out = in1 + in2 - 2*(in1 AND in2)

    For integer checking, we verify: out = 1 iff exactly one input is 1. -/
def xor_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.xor_gate in1.val in2.val out.val

/-- NAND gate constraint: out = ¬(in1 ∧ in2)
    For 0/1 variables: out = 1 - (in1 AND in2)
    Equivalent to: out = 0 iff both inputs are 1. -/
def nand_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.nand_gate in1.val in2.val out.val

/-- NOR gate constraint: out = ¬(in1 ∨ in2)
    For 0/1 variables: out = 1 - (in1 OR in2)
    Equivalent to: out = 1 iff both inputs are 0. -/
def nor_gate {num_vars : ℕ} (in1 in2 out : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.nor_gate in1.val in2.val out.val

end BooleanGates

/-! ### Multi-Input Logical Operations -/

section MultiInputLogic

variable {num_vars : ℕ}

/-- AND-all constraint: result = ∧ vars
    Result is 1 iff all variables in vars are 1.
    Semantically: result = min(vars) -/
def and_all {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (result : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.and_all (scope.toList.map (·.val)) result.val

/-- OR-all constraint: result = ∨ vars
    Result is 1 iff at least one variable in vars is 1. -/
def or_all {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (result : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.or_all (scope.toList.map (·.val)) result.val

/-- XOR-all constraint: result = ⊕ vars (n-ary XOR / parity)
    Result is 1 iff an odd number of variables in vars are 1.
    This is the parity function used in ECC and cryptography. -/
def xor_all {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (result : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.xor_all (scope.toList.map (·.val)) result.val

end MultiInputLogic

/-! ### Implication and Equivalence Constraints -/

section ImplicationConstraints

variable {num_vars : ℕ}

/-- Implication constraint: premise ⇒ conclusion
    For 0/1 variables: if premise=1 then conclusion=1.
    Encodes as: conclusion ≥ premise -/
def implies {num_vars : ℕ} (premise conclusion : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.implies premise.val conclusion.val

/-- If-and-only-if constraint: var1 ↔ var2
    For 0/1 variables: var1 and var2 must have the same value.
    Encodes as: var1 = var2 -/
def iff {num_vars : ℕ} (var1 var2 : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.iff var1.val var2.val

/-- If-then constraint: if var = value then next_var = next_value.
    Reified implication for state transitions: (var = value) → (next_var = next_value) -/
def if_then {num_vars : ℕ}
    (var : VarType num_vars) (value : ℤ)
    (next_var : VarType num_vars) (next_value : ℤ) :
    IntConstraint num_vars :=
  IntConstraint.if_then var.val value next_var.val next_value

/-- If-then-or constraint: if var = value then next_var ∈ allowed_values.
    Disjunctive implication for non-deterministic state transitions:
    (var = value) → (next_var ∈ allowed_values) -/
def if_then_or {num_vars : ℕ}
    (var : VarType num_vars) (value : ℤ)
    (next_var : VarType num_vars) (allowed_values : List ℤ) :
    IntConstraint num_vars :=
  IntConstraint.if_then_or var.val value next_var.val allowed_values

end ImplicationConstraints

/-! ### Cardinality Constraints -/

section CardinalityConstraints

variable {num_vars : ℕ}

/-- At-least-k constraint: at least k variables must be 1.
    For 0/1 variables: sum(vars) ≥ k -/
def at_least_k {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (k : ℕ) :
    IntConstraint num_vars :=
  IntConstraint.at_least_k (scope.toList.map (·.val)) k

/-- At-most-k constraint: at most k variables can be 1.
    For 0/1 variables: sum(vars) ≤ k -/
def at_most_k {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (k : ℕ) :
    IntConstraint num_vars :=
  IntConstraint.at_most_k (scope.toList.map (·.val)) k

/-- Exactly-k constraint: exactly k variables must be 1.
    For 0/1 variables: sum(vars) = k -/
def exactly_k {n : ℕ} (scope : _root_.Vector (VarType num_vars) n) (k : ℕ) :
    IntConstraint num_vars :=
  IntConstraint.exactly_k (scope.toList.map (·.val)) k

end CardinalityConstraints

/-! ### Arithmetic Constraints with Variable Targets -/

section VariableTargetConstraints

variable {num_vars : ℕ}

/-- Product constraint with variable target: product(vars) op target_var
    Computes the product of all variables in the scope and compares with target variable. -/
def product_rel_var {n : ℕ}
    (scope : _root_.Vector (VarType num_vars) n)
    (op : RelOp)
    (target : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.product_rel_var (scope.toList.map (·.val)) op target.val

/-- Linear constraint with variable target: Σ(coeffs[i] * vars[i]) op target_var -/
def linear_rel_var {n : ℕ}
    (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n)
    (op : RelOp)
    (target : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.linear_rel_var (scope.toList.map (·.val)) coeffs.toList op target.val

/-- Sum constraint with variable target: sum(vars) op target_var -/
def sum_rel_var {n : ℕ}
    (scope : _root_.Vector (VarType num_vars) n)
    (op : RelOp)
    (target : VarType num_vars) :
    IntConstraint num_vars :=
  IntConstraint.sum_rel_var (scope.toList.map (·.val)) op target.val

/-- Convenient aliases for common cases -/
def product_eq_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : IntConstraint num_vars :=
  product_rel_var scope .EQ target

def product_ne_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : IntConstraint num_vars :=
  product_rel_var scope .NE target

def linear_eq_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : VarType num_vars) : IntConstraint num_vars :=
  linear_rel_var scope coeffs .EQ target

def linear_ne_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (coeffs : _root_.Vector ℤ n) (target : VarType num_vars) : IntConstraint num_vars :=
  linear_rel_var scope coeffs .NE target

def sum_eq_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : IntConstraint num_vars :=
  sum_rel_var scope .EQ target

def sum_ne_var {n : ℕ} (scope : _root_.Vector (VarType num_vars) n)
    (target : VarType num_vars) : IntConstraint num_vars :=
  sum_rel_var scope .NE target

end VariableTargetConstraints

/-! ### Scheduling Constraints -/

section SchedulingConstraints

/-- Disjunctive constraint: tasks on a unary resource must not overlap.
    For all pairs (i,j): (start[i] + duration[i] ≤ start[j]) ∨ (start[j] + duration[j] ≤ start[i])
    Used for machine mutex in job-shop scheduling. -/
def disjunctive {num_vars : ℕ}
    (tasks : List (VarType num_vars))
    (durations : List ℤ) :
    IntConstraint num_vars :=
  -- Scope includes all task variables
  IntConstraint.disjunctive (tasks.map (·.val)) durations

end SchedulingConstraints

/-! ### Convenience Functions -/

section Convenience

/-- Create alldifferent constraint for all variables -/
def alldifferent_all (num_vars : ℕ) : IntConstraint num_vars :=
  alldifferent (_root_.Vector.ofFn id)

/-- Create sum constraint for all variables -/
def sum_all_eq (num_vars : ℕ) (target : ℤ) : IntConstraint num_vars :=
  sum_eq (_root_.Vector.ofFn id) target

end Convenience

end CSP.L2S
