import CSP.Core
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Vector.Basic

namespace CSP.L2S

/-!
# L2M (Lean-to-MiniZinc) Core

Unified CSP framework combining Homogeneous integer domains with Tagged constraints
for direct MiniZinc translation. This eliminates the two-layer structure and provides
a single `IntCSP` type that is both proof-ready and MiniZinc-translatable.

## Design

- **Single Structure**: One `IntCSP` type (not base + tagged)
- **Dual Representation**: Each constraint has semantic pattern + dynamic checker
- **Integer Domains**: All variables have type `ℤ` (unlimited range, negatives supported)
- **Direct Translation**: MiniZinc generation without structure conversion


-/

-- ============================================================================
-- Type Aliases and Foundations
-- ============================================================================

/-- Integer domain for all variables -/
abbrev IntDomain := ℤ

/-- Variable indices are finite -/
abbrev VarType (n : ℕ) := Fin n

/-- DecidableEq instance for variable indices -/
instance {n : ℕ} : DecidableEq (VarType n) := inferInstance

/-- Abbreviation for homogeneous constraints -/
abbrev IntConstraint (n : ℕ) :=
  DynamicConstraint (VarType n) (fun _ => IntDomain)

/-- Abbreviation for homogeneous assignments -/
abbrev IntAssignment (n : ℕ) :=
  VarType n → IntDomain

-- ============================================================================
-- Relational Operators (for sum and other constraints)
-- ============================================================================

/-- Relational operators for constraints -/
inductive RelOp where
  | EQ  -- Equal
  | NE  -- Not equal
  | LT  -- Less than
  | LE  -- Less than or equal
  | GT  -- Greater than
  | GE  -- Greater than or equal
  deriving Repr, DecidableEq

-- ============================================================================
-- Constraint Patterns (Semantic Representation)
-- ============================================================================

/--
Semantic patterns for constraint types. These enable MiniZinc translation
by capturing the high-level structure of constraints.
-/
inductive ConstraintPattern (num_vars : ℕ)
  -- Global constraints
  | alldifferent (vars : List ℕ)
  | alldifferentOffset (vars : List ℕ) (offsets : List ℤ)  -- For diagonal constraints
  | increasing (vars : List ℕ)  -- Variables in non-decreasing order

  -- Arithmetic constraints
  | sum (vars : List ℕ) (op : RelOp) (target : ℤ)
  | linear (vars : List ℕ) (coeffs : List ℤ) (op : RelOp) (target : ℤ)  -- Weighted sum with coefficients
  | count (vars : List ℕ) (value : ℤ) (n : ℕ)
  | count_var (vars : List ℕ) (value : ℤ) (count_var : ℕ)  -- Count with variable result (for magic sequence)
  | element (index : ℕ) (array : List ℤ) (result : ℕ)
  | maximum (vars : List ℕ) (maxVar : ℕ)
  | minimum (vars : List ℕ) (minVar : ℕ)

  -- Bound constraints (for variable domain specification)
  | bound (var : ℕ) (lb ub : ℤ)

  -- Binary comparison constraints
  | eq (var1 var2 : ℕ)  -- var1 = var2
  | ne (var1 var2 : ℕ)  -- var1 ≠ var2
  | lt (var1 var2 : ℕ)  -- var1 < var2
  | le (var1 var2 : ℕ)  -- var1 ≤ var2
  | gt (var1 var2 : ℕ)  -- var1 > var2
  | ge (var1 var2 : ℕ)  -- var1 ≥ var2

  -- Unary comparison constraints (variable to constant)
  | eq_const (var : ℕ) (value : ℤ)  -- var = value
  | ne_const (var : ℕ) (value : ℤ)  -- var ≠ value
  | lt_const (var : ℕ) (value : ℤ)  -- var < value
  | le_const (var : ℕ) (value : ℤ)  -- var ≤ value
  | gt_const (var : ℕ) (value : ℤ)  -- var > value
  | ge_const (var : ℕ) (value : ℤ)  -- var ≥ value

  -- Logical/Disjunctive constraints
  | schur_triple (var1 var2 var3 : ℕ)  -- Not all three variables equal: x ≠ y ∨ x ≠ z ∨ y ≠ z

  -- Absolute value constraints
  | abs_diff_rel (var1 var2 : ℕ) (op : RelOp) (target : ℤ)  -- |var1 - var2| op target
  | abs_diff_var (var1 var2 result : ℕ)  -- result = |var1 - var2|

  -- Modulo constraints
  | modulo (var : ℕ) (n k : ℤ)  -- var mod n = k

  -- Sliding window constraints
  | sliding_sum (vars : List ℕ) (window_size : ℕ) (op : RelOp) (target : ℤ)  -- For each window of size k, sum op target

  -- Boolean gate constraints (for 0/1 valued variables)
  | not_gate (in1 out : ℕ)      -- out = ¬in (unary negation)
  | and_gate (in1 in2 out : ℕ)  -- out = in1 ∧ in2
  | or_gate (in1 in2 out : ℕ)   -- out = in1 ∨ in2
  | xor_gate (in1 in2 out : ℕ)  -- out = in1 ⊕ in2
  | nand_gate (in1 in2 out : ℕ) -- out = ¬(in1 ∧ in2)
  | nor_gate (in1 in2 out : ℕ)  -- out = ¬(in1 ∨ in2)

  -- Multi-input logical operations
  | and_all (vars : List ℕ) (result : ℕ)  -- result = ∧ vars
  | or_all (vars : List ℕ) (result : ℕ)   -- result = ∨ vars
  | xor_all (vars : List ℕ) (result : ℕ)  -- result = ⊕ vars (parity)

  -- Implication and equivalence
  | implies (premise conclusion : ℕ)  -- premise ⇒ conclusion
  | iff (var1 var2 : ℕ)               -- var1 ↔ var2
  | if_then (var : ℕ) (value : ℤ) (next_var : ℕ) (next_value : ℤ)  -- if var=value then next_var=next_value
  | if_then_or (var : ℕ) (value : ℤ) (next_var : ℕ) (allowed_values : List ℤ)  -- if var=value then next_var ∈ allowed_values

  -- Cardinality constraints (for Boolean variables)
  | at_least_k (vars : List ℕ) (k : ℕ)  -- sum(vars) ≥ k
  | at_most_k (vars : List ℕ) (k : ℕ)   -- sum(vars) ≤ k
  | exactly_k (vars : List ℕ) (k : ℕ)   -- sum(vars) = k

  -- Arithmetic constraints with variable targets (not constants)
  | sum_rel_var (vars : List ℕ) (op : RelOp) (target_var : ℕ)  -- sum(vars) op target_var
  | linear_rel_var (vars : List ℕ) (coeffs : List ℤ) (op : RelOp) (target_var : ℕ)  -- Σ(coeffs[i]*vars[i]) op target_var
  | product_rel_var (vars : List ℕ) (op : RelOp) (target_var : ℕ)  -- product(vars) op target_var

  -- Scheduling constraints
  | disjunctive (tasks : List ℕ) (durations : List ℤ)  -- Tasks on unary resource must not overlap

  -- Unknown pattern (fallback)
  | unknown (arity : ℕ) (scope : List ℕ)
  deriving Repr

-- ============================================================================
-- Tagged Constraint (Dual Representation)
-- ============================================================================

/--
Tagged constraint bundles semantic pattern with dynamic checker.

The dual representation enables:
- **Pattern**: High-level structure for MiniZinc translation
- **Dynamic**: Executable checker for Lean proofs and verification
-/
structure TaggedConstraint (num_vars : ℕ) where
  /-- The semantic pattern for translation -/
  pattern : ConstraintPattern num_vars
  /-- The dynamic checker for proof verification -/
  dynamic : IntConstraint num_vars

-- ============================================================================
-- Unified Homogeneous CSP Structure
-- ============================================================================

/--
Unified Homogeneous CSP structure combining integer domains with tagged constraints.

This single structure eliminates the two-layer approach:
- No separate "base" CSP and "tagged" wrapper
- Directly translatable to MiniZinc
- Directly usable in proofs

All variables have integer domain `ℤ` with bounds specified via bound constraint patterns.
-/
structure IntCSP where
  /-- Number of variables in the CSP -/
  num_vars : ℕ
  /-- List of tagged constraints (pattern + checker) -/
  constraints : List (TaggedConstraint num_vars)

namespace IntCSP

-- ============================================================================
-- Solution Checking
-- ============================================================================

/-- Check if a constraint is satisfied by an assignment -/
def satisfiesConstraintInt (c : TaggedConstraint n) (assignment : IntAssignment n) : Prop :=
  satisfies_dynamic_constraint c.dynamic assignment

/-- Check if an assignment is a solution to the CSP -/
def isSolutionInt (csp : IntCSP) (assignment : IntAssignment csp.num_vars) : Prop :=
  ∀ c ∈ csp.constraints, satisfiesConstraintInt c assignment

/-- Check if a CSP is satisfiable (has at least one solution) -/
def isSatisfiableInt (csp : IntCSP) : Prop :=
  ∃ assignment, isSolutionInt csp assignment

-- ============================================================================
-- Bound Extraction (for MiniZinc Variable Declarations)
-- ============================================================================

/-- Extract bounds for a variable from bound constraint patterns -/
def extractVariableBounds (csp : IntCSP)
    (var : VarType csp.num_vars) : ℤ × ℤ :=
  -- Scan through constraints looking for bound patterns for this variable
  let bounds := csp.constraints.filterMap fun tc =>
    match tc.pattern with
    | ConstraintPattern.bound v lb ub => if v = var.val then some (lb, ub) else none
    | _ => none

  -- If we found bounds, use them; otherwise default to reasonable range
  match bounds with
  | [] => (-1000, 1000)  -- Default range for unbounded variables
  | (lb, ub) :: _ => (lb, ub)  -- Use first bound found

/-- Extract bounds for all variables -/
def extractAllBounds (csp : IntCSP) :
    VarType csp.num_vars → (ℤ × ℤ) :=
  fun var => extractVariableBounds csp var

-- ============================================================================
-- CSP Construction
-- ============================================================================

/-- Create empty CSP with specified number of variables -/
def mkEmpty (num_vars : ℕ) : IntCSP where
  num_vars := num_vars
  constraints := []

/-- Add a constraint to an existing CSP -/
def addConstraint (csp : IntCSP)
    (constraint : TaggedConstraint csp.num_vars) : IntCSP :=
  { csp with constraints := constraint :: csp.constraints }

/-- Add multiple constraints -/
def addConstraints (csp : IntCSP)
    (new_constraints : List (TaggedConstraint csp.num_vars)) : IntCSP :=
  { csp with constraints := new_constraints ++ csp.constraints }



-- ============================================================================
-- Utility Functions
-- ============================================================================

/-- Count constraints in a CSP -/
def constraintCount (csp : IntCSP) : ℕ :=
  csp.constraints.length

/-- Get all variable indices -/
def allVars (csp : IntCSP) : List (VarType csp.num_vars) :=
  List.ofFn id

/-- Helper function to convert a list of natural numbers to a vector of Fin with bounds checking.
    Returns Some with the vector if all inputs are within bounds, None otherwise. -/
def listToFinVector (inputs : List ℕ) (num_nodes : ℕ) :
    Option (Σ n : ℕ, _root_.Vector (Fin num_nodes) n) :=
  -- Filter and map inputs to Fin num_nodes, keeping only valid ones
  let fin_list : List (Fin num_nodes) := inputs.filterMap fun inp =>
    if h : inp < num_nodes then some ⟨inp, h⟩ else none
  -- Check that no inputs were filtered out (all were valid) and list is non-empty
  if fin_list.length = inputs.length ∧ inputs.length > 0 then
    -- Convert to array then to vector
    let arr := Array.mk fin_list
    have h_size : arr.size = fin_list.length := by rfl
    some ⟨fin_list.length, ⟨arr, h_size⟩⟩
  else
    none

end IntCSP

-- ============================================================================
-- Extracting Constraints from Built CSPs
-- ============================================================================

/-- Get all constraints from a CSP -/
def getConstraints (csp : IntCSP) : List (TaggedConstraint csp.num_vars) :=
  csp.constraints

/-- Extract all constraint patterns (semantic representation) -/
def getPatterns (csp : IntCSP) : List (ConstraintPattern csp.num_vars) :=
  csp.constraints.map (·.pattern)

/-- Count total number of constraints -/
def countConstraints (csp : IntCSP) : ℕ :=
  csp.constraints.length

/-- Count constraints of a specific type -/
def countConstraintsByPattern (csp : IntCSP)
    (pred : ConstraintPattern csp.num_vars → Bool) : ℕ :=
  (getPatterns csp).filter pred |>.length

/-- Count bound constraints -/
def countBoundConstraints (csp : IntCSP) : ℕ :=
  countConstraintsByPattern csp fun p =>
    match p with
    | ConstraintPattern.bound _ _ _ => true
    | _ => false



-- ============================================================================
-- Basic Examples
-- ============================================================================

section Examples

/-- Example: Simple 2-variable CSP with no constraints -/
def example_2var : IntCSP :=
  IntCSP.mkEmpty 2

/-- Example: CSP with bound constraints -/
def example_with_bounds : IntCSP :=
  let csp := IntCSP.mkEmpty 3
  -- Note: In practice, bounds are added via Builder API
  -- This is just for illustration
  csp

end Examples

end CSP.L2S
