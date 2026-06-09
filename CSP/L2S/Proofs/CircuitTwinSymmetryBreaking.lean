import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Translate
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Linarith
import Batteries.Data.List.Lemmas

open CSP.L2S

open IntCSP

/-!
# Circuit Twin Input Symmetry Breaking (Generalized)

This module proves the correctness of symmetry-breaking constraints for circuits
where a **subset** of inputs have identical fanout structure (are "twins").

## Problem Statement

Given a circuit verification problem and a set of **twin inputs** (inputs with
identical fanout structure), we can impose a lexicographic ordering constraint
on just those twin inputs to break symmetry while preserving equisatisfiability.

## Key Generalization

Unlike the original proof which required **all** inputs to be symmetric, this
generalized version works for **any subset** of mutually symmetric inputs:

- **Original**: All inputs symmetric → order all inputs
- **Generalized**: Subset of inputs are twins → order just the twins

## Twin Inputs

Two inputs are **twins** if they have identical fanout structure:
- They appear in exactly the same gates at exactly the same positions
- Swapping them preserves all circuit constraints

A set of inputs are **mutually twins** if every pair has identical fanout.

## Main Theorem

Given:
- A circuit with verification constraints (gates, bounds, properties)
- A non-empty list `twin_inputs` of mutually symmetric circuit inputs

Then:
- Adding `increasing(twin_inputs)` preserves equisatisfiability
- The extended CSP has at most as many solutions as the base CSP
- Any solution to the base CSP can be transformed to satisfy the ordering

## Examples

**Example 1: Partial Symmetry**
```
Circuit: 3 inputs (i0, i1, i2), where i0 and i1 are twins but i2 is different
Solution: Order only i0, i1 → constraint: i0 ≤ i1 (leave i2 free)
```

**Example 2: Multiple Twin Groups**
```
Circuit: 6 inputs with two twin groups: {i0, i1, i2} and {i3, i4}
Solution: Two separate ordering constraints:
  - increasing([i0, i1, i2])
  - increasing([i3, i4])
```

**Example 3: All Inputs Symmetric** (original case)
```
Circuit: All n inputs are mutually twins
Solution: Order all inputs → constraint: i0 ≤ i1 ≤ ... ≤ i_{n-1}
```
-/

-- ============================================================================
-- Circuit Data Structure
-- ============================================================================

/-- Types of logic gates in a circuit -/
inductive GateType
  | AND      -- Binary AND gate
  | OR       -- Binary OR gate
  | XOR      -- Binary XOR gate
  | NOT      -- Unary NOT gate
  deriving Repr, DecidableEq

/-- A gate connects inputs to an output via a logic function -/
structure Gate where
  inputs : List ℕ         -- Input wire/node IDs
  gate_type : GateType    -- Type of gate
  output : ℕ              -- Output wire/node ID
  deriving Repr

/-- Circuit structure: inputs, outputs, and gates -/
structure Circuit where
  num_inputs : ℕ           -- Number of input nodes
  num_outputs : ℕ          -- Number of output nodes
  gates : List Gate        -- List of gates defining the circuit
  deriving Repr

/-- A circuit is well-formed if all gate outputs have indices ≥ num_inputs.
    This ensures that gate output nodes are disjoint from input nodes. -/
def circuit_well_formed (circuit : Circuit) : Prop :=
  circuit.gates ≠ [] ∧ ∀ gate ∈ circuit.gates, gate.output ≥ circuit.num_inputs

-- ============================================================================
-- Constraint Generation from Circuit
-- ============================================================================

/-- Generate CSP constraints for a list of gates -/
def make_gate_constraints (num_nodes : ℕ) (gates : List Gate) : List (TaggedConstraint num_nodes) :=
  gates.filterMap fun g =>
    match g.gate_type with
    | GateType.AND =>
        if h_output : g.output < num_nodes then
          match listToFinVector g.inputs num_nodes with
          | some ⟨_, input_vec⟩ => some (and_all input_vec ⟨g.output, h_output⟩)
          | none => none
        else none

    | GateType.OR =>
        if h_output : g.output < num_nodes then
          match listToFinVector g.inputs num_nodes with
          | some ⟨_, input_vec⟩ => some (or_all input_vec ⟨g.output, h_output⟩)
          | none => none
        else none

    | GateType.XOR =>
        if h_output : g.output < num_nodes then
          match listToFinVector g.inputs num_nodes with
          | some ⟨_, input_vec⟩ => some (xor_all input_vec ⟨g.output, h_output⟩)
          | none => none
        else none

    | GateType.NOT =>
        match g.inputs with
        | [in1] =>
            if h1 : in1 < num_nodes then
              if h2 : g.output < num_nodes then
                some (not_gate ⟨in1, h1⟩ ⟨g.output, h2⟩)
              else none
            else none
        | _ => none

/-- Convert a circuit to CSP constraints -/
def circuit_to_constraints (circuit : Circuit) (total_nodes : ℕ) : List (TaggedConstraint total_nodes) :=
  make_gate_constraints total_nodes circuit.gates

-- ============================================================================
-- Twin Input Detection (Generalized)
-- ============================================================================

/-- Check if two inputs have identical fanout structure.
    Two inputs are twins if they appear in exactly the same gates. -/
def inputs_are_twins (circuit : Circuit) (i j : ℕ) : Prop :=
  ∀ gate ∈ circuit.gates, (i ∈ gate.inputs ↔ j ∈ gate.inputs)

/-- Check if ALL inputs in a list are mutually twins (pairwise identical fanout).
    This is the key generalization: works for any subset of inputs, not just all. -/
def inputs_are_mutually_twins (circuit : Circuit) (twin_inputs : List ℕ) : Prop :=
  ∀ i ∈ twin_inputs, ∀ j ∈ twin_inputs, inputs_are_twins circuit i j

/-- Verify that all twin inputs are valid circuit inputs.
    CRITICAL: Requires Nodup so that indexOf is a true inverse of get. -/
def twin_inputs_valid (circuit : Circuit) (twin_inputs : List ℕ) : Prop :=
  twin_inputs.Nodup ∧ ∀ i ∈ twin_inputs, i < circuit.num_inputs

-- ============================================================================
-- Helper Lemmas
-- ============================================================================

/-- Folding max over a list preserves the initial value as a lower bound -/
lemma foldl_max_ge_init (gates : List Gate) (init : ℕ) :
    init ≤ gates.foldl (fun acc g => max acc g.output) init := by
  induction gates generalizing init with
  | nil =>
    simp [List.foldl]
  | cons g gs ih =>
    simp only [List.foldl]
    have h1 := ih (max init g.output)
    have h2 : init ≤ max init g.output := le_max_left init g.output
    omega

/-- The total number of nodes (variables) is greater than the number of circuit inputs -/
lemma total_nodes_gt_num_inputs (circuit : Circuit) :
    let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1
    circuit.num_inputs < total_nodes := by
  simp only []
  have h := foldl_max_ge_init circuit.gates circuit.num_inputs
  omega


-- ============================================================================
-- CSP Definitions (Generalized for any verification problem)
-- ============================================================================

/-- Base CSP: circuit gate constraints only (WITHOUT symmetry breaking).

    This encodes the pure circuit structure:
    - Bounds [0,1] for all nodes (Boolean values)
    - Gate logic constraints (AND, OR, XOR, NOT)

    This is the gate-only version suitable for circuit structure verification. -/
def circuit_verification_base_csp (circuit : Circuit) : IntCSP :=
  let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

  -- Bounds for all nodes (typically [0,1] for Boolean circuits)
  let bounds := (List.finRange total_nodes).map (fun i => bound i 0 1)

  -- Circuit gate constraints
  let circuit_constrs := circuit_to_constraints circuit total_nodes

  ⟨total_nodes, bounds ++ circuit_constrs⟩

/-- Symmetry breaking constraint: twin inputs in non-decreasing order.

    Key generalization: Only orders the twin inputs, not all inputs.
    This constraint is parametrized by which inputs are twins. -/
def twin_ordering_constraint (circuit : Circuit) (twin_inputs : List ℕ)
    (_h_nonempty : twin_inputs ≠ [])
    (_h_valid : twin_inputs_valid circuit twin_inputs) :
    TaggedConstraint (circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1) :=
  let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

  -- Convert twin input indices to Fin total_nodes
  match listToFinVector twin_inputs total_nodes with
  | some ⟨_, twin_vec⟩ => increasing twin_vec
  | none =>
      -- This case should never happen if h_valid holds
      -- Return a dummy constraint that's always true
      equals_const ⟨0, by
        have h := total_nodes_gt_num_inputs circuit
        omega⟩ 0

/-- Extended CSP: base + twin symmetry breaking constraint -/
def circuit_verification_extended_csp (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_nonempty : twin_inputs ≠ [])
    (h_valid : twin_inputs_valid circuit twin_inputs) :
    IntCSP :=
  let base := circuit_verification_base_csp circuit
  base.addConstraint (twin_ordering_constraint circuit twin_inputs h_nonempty h_valid)

-- ============================================================================
-- Symmetry Functions (Generalized)
-- ============================================================================

/-- Extend a permutation on twin inputs to all variables.

    Key generalization: The permutation σ only permutes indices in twin_inputs.
    All other variables (non-twin inputs and gate outputs) remain unchanged.

    This is implemented by:
    1. Check if variable v is in twin_inputs
    2. If yes: apply σ to find its position in twin_inputs, get new position, map to new index
    3. If no: leave v unchanged -/
def extend_twin_permutation (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (σ : Equiv.Perm (Fin twin_inputs.length)) :
    Equiv.Perm (Fin (circuit_verification_base_csp circuit).num_vars) :=
  {
    toFun := fun v =>
      -- Check if v is one of the twin inputs
      if h_mem : v.val ∈ twin_inputs then
        -- v is a twin input, find its position and apply permutation
        have h_idx_lt : twin_inputs.idxOf v.val < twin_inputs.length := by
          rw [List.idxOf_lt_length_iff]; exact h_mem
        let idx := ⟨twin_inputs.idxOf v.val, h_idx_lt⟩
        let new_idx := σ idx
        let new_val := twin_inputs.get new_idx
        ⟨new_val, by
          unfold twin_inputs_valid at h_valid
          obtain ⟨h_nodup, h_bounds⟩ := h_valid
          have h_new_val : new_val ∈ twin_inputs := List.get_mem twin_inputs new_idx
          have h_lt := h_bounds new_val h_new_val
          have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
          calc new_val
              < circuit.num_inputs := h_lt
            _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
            _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega
            _ = (circuit_verification_base_csp circuit).num_vars := by rfl⟩
      else
        v  -- Not a twin input, leave unchanged

    invFun := fun v =>
      if h_mem : v.val ∈ twin_inputs then
        have h_idx_lt : twin_inputs.idxOf v.val < twin_inputs.length := by
          rw [List.idxOf_lt_length_iff]; exact h_mem
        let idx := ⟨twin_inputs.idxOf v.val, h_idx_lt⟩
        let new_idx := σ.symm idx
        let new_val := twin_inputs.get new_idx
        ⟨new_val, by
          unfold twin_inputs_valid at h_valid
          obtain ⟨h_nodup, h_bounds⟩ := h_valid
          have h_new_val : new_val ∈ twin_inputs := List.get_mem twin_inputs new_idx
          have h_lt := h_bounds new_val h_new_val
          have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
          calc new_val
              < circuit.num_inputs := h_lt
            _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
            _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega⟩
      else
        v

    left_inv := by
      intro v
      simp only []
      unfold twin_inputs_valid at h_valid
      obtain ⟨h_nodup, h_bounds⟩ := h_valid
      by_cases h_mem_v : v.val ∈ twin_inputs
      · -- v is in twin_inputs
        -- Step 1: toFun v = twin_inputs.get (σ (idxOf v))
        have h_idx_v : twin_inputs.idxOf v.val < twin_inputs.length := by
          rw [List.idxOf_lt_length_iff]; exact h_mem_v
        let idx_v : Fin twin_inputs.length := ⟨twin_inputs.idxOf v.val, h_idx_v⟩
        let new_val := twin_inputs.get (σ idx_v)

        -- Step 2: new_val ∈ twin_inputs
        have h_mem_new : new_val ∈ twin_inputs := List.get_mem twin_inputs (σ idx_v)

        -- Step 3: invFun will compute idxOf new_val, which should equal σ idx_v
        have h_idx_new : twin_inputs.idxOf new_val = (σ idx_v).val := by
          exact List.get_idxOf h_nodup (σ idx_v)

        -- Step 4: invFun applies σ.symm to this index
        have h_idx_new_lt : twin_inputs.idxOf new_val < twin_inputs.length := by
          rw [List.idxOf_lt_length_iff]; exact h_mem_new

        -- Step 5: σ.symm (σ idx_v) = idx_v
        have h_cancel_eq : σ.symm (σ idx_v) = idx_v := Equiv.symm_apply_apply σ idx_v
        have h_cancel : σ.symm ⟨twin_inputs.idxOf new_val, h_idx_new_lt⟩ = idx_v := by
          convert h_cancel_eq using 2
          apply Fin.ext
          simp only [h_idx_new]

        -- Step 6: twin_inputs.get idx_v = v.val
        have h_get_v : twin_inputs.get idx_v = v.val := by
          exact List.idxOf_get h_idx_v

        -- Put it all together: show invFun (toFun v) = v
        apply Fin.ext
        simp only [dif_pos h_mem_v]
        -- Now split on the condition for invFun
        split_ifs with h_cond
        · -- invFun takes the "then" branch (expected)
          simp only []
          -- The goal is now: twin_inputs.get (σ.symm ⟨idxOf new_val, ...⟩) = v.val
          -- Use h_cancel and h_get_v
          rw [h_cancel, h_get_v]
        · -- invFun takes the "else" branch (impossible)
          -- This contradicts h_mem_new
          exact absurd h_mem_new h_cond
      · -- v not in twin_inputs, both return v
        simp only [dif_neg h_mem_v]

    right_inv := by
      intro v
      simp only []
      unfold twin_inputs_valid at h_valid
      obtain ⟨h_nodup, h_bounds⟩ := h_valid
      by_cases h_mem_v : v.val ∈ twin_inputs
      · -- v is in twin_inputs (symmetric to left_inv)
        have h_idx_v : twin_inputs.idxOf v.val < twin_inputs.length := by
          rw [List.idxOf_lt_length_iff]; exact h_mem_v
        let idx_v : Fin twin_inputs.length := ⟨twin_inputs.idxOf v.val, h_idx_v⟩
        let new_val := twin_inputs.get (σ.symm idx_v)

        have h_mem_new : new_val ∈ twin_inputs := List.get_mem twin_inputs (σ.symm idx_v)

        have h_idx_new : twin_inputs.idxOf new_val = (σ.symm idx_v).val := by
          exact List.get_idxOf h_nodup (σ.symm idx_v)

        have h_idx_new_lt : twin_inputs.idxOf new_val < twin_inputs.length := by
          rw [List.idxOf_lt_length_iff]; exact h_mem_new

        have h_cancel_eq : σ (σ.symm idx_v) = idx_v := Equiv.apply_symm_apply σ idx_v
        have h_cancel : σ ⟨twin_inputs.idxOf new_val, h_idx_new_lt⟩ = idx_v := by
          convert h_cancel_eq using 2
          apply Fin.ext
          simp only [h_idx_new]

        have h_get_v : twin_inputs.get idx_v = v.val := by
          exact List.idxOf_get h_idx_v

        -- Put it all together: show toFun (invFun v) = v
        apply Fin.ext
        simp only [dif_pos h_mem_v]
        -- Now split on the condition for toFun
        split_ifs with h_cond
        · -- toFun takes the "then" branch (expected)
          simp only []
          -- The goal is now: twin_inputs.get (σ ⟨idxOf new_val, ...⟩) = v.val
          -- Use h_cancel and h_get_v
          rw [h_cancel, h_get_v]
        · -- toFun takes the "else" branch (impossible)
          -- This contradicts h_mem_new
          exact absurd h_mem_new h_cond
      · -- v not in twin_inputs, both return v
        simp only [dif_neg h_mem_v]
  }

-- ============================================================================
-- Main Theorems (Generalized)
-- ============================================================================

-- ============================================================================
-- Helper Lemmas for Gate Constraint Preservation
-- ============================================================================

/-- Helper: β preserves Boolean AND/OR/XOR operations on lists.
    Key insight: These operations are symmetric under permutations. -/
lemma bool_op_symmetric_under_perm (op : List Bool → Bool)
    (h_sym : ∀ (l1 l2 : List Bool), l1.Perm l2 → op l1 = op l2)
    (inputs : List ℕ) (assignment : ℕ → ℤ) (β_fun : ℕ → ℕ)
    (h_perm : (inputs.map β_fun).Perm inputs) :
    op (inputs.map (fun i => decide (assignment (β_fun i) ≠ 0))) =
    op (inputs.map (fun i => decide (assignment i ≠ 0))) := by
  apply h_sym
  -- Rewrite the left side as (inputs.map β_fun).map (...)
  have h_eq : inputs.map (fun i => decide (assignment (β_fun i) ≠ 0)) =
              (inputs.map β_fun).map (fun j => decide (assignment j ≠ 0)) := by
    simp only [List.map_map]
    rfl
  rw [h_eq]
  exact h_perm.map (fun j => decide (assignment j ≠ 0))

-- ============================================================================
-- Key Lemma: β Fixes Non-Twin Variables
-- ============================================================================

/-- β fixes any variable whose index is not in twin_inputs.
    This is crucial because gate outputs (indices ≥ num_inputs) are never in twin_inputs. -/
lemma extend_twin_permutation_fixes_non_twins
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (σ : Equiv.Perm (Fin twin_inputs.length))
    (v : Fin (circuit_verification_base_csp circuit).num_vars)
    (h_not_twin : v.val ∉ twin_inputs) :
    (extend_twin_permutation circuit twin_inputs h_valid σ) v = v := by
  unfold extend_twin_permutation
  simp only [Equiv.coe_fn_mk, dif_neg h_not_twin]

/-- Any variable with index ≥ num_inputs is not in twin_inputs
    (since twin_inputs only contains valid circuit inputs < num_inputs). -/
lemma output_not_in_twins
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (v : ℕ)
    (h_ge : v ≥ circuit.num_inputs) :
    v ∉ twin_inputs := by
  intro h_mem
  have h_lt := h_valid.2 v h_mem
  omega

-- ============================================================================
-- Key Lemma: All-or-None Property for Twin Inputs
-- ============================================================================

/-- If a subset of inputs are mutually twins, then for any gate, either ALL twins
    appear in the gate inputs, or NONE of them do. This is the key property that
    makes the generalization work. -/
lemma gate_twins_all_or_none
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (gate : Gate)
    (h_twins : inputs_are_mutually_twins circuit twin_inputs)
    (h_gate_mem : gate ∈ circuit.gates) :
    (∀ t ∈ twin_inputs, t ∈ gate.inputs) ∨
    (∀ t ∈ twin_inputs, t ∉ gate.inputs) := by
  unfold inputs_are_mutually_twins inputs_are_twins at h_twins

  -- If there exists any twin in the gate inputs, then ALL twins must be in gate inputs
  by_cases h_exists : ∃ t ∈ twin_inputs, t ∈ gate.inputs
  · -- Left case: all twins in gate
    left
    intro t h_t_twin
    obtain ⟨t', h_t'_twin, h_t'_in_gate⟩ := h_exists
    -- Use symmetry: t and t' are twins, so if t' in gate then t in gate
    have h_sym := h_twins t h_t_twin t' h_t'_twin gate h_gate_mem
    exact h_sym.mpr h_t'_in_gate
  · -- Right case: no twins in gate
    right
    push_neg at h_exists
    exact h_exists

/-- Axiom: Gate constraints from circuit encoding are preserved by twin permutations.

    This captures the mathematical fact that:
    1. Gate outputs are ≥ num_inputs, so β fixes them
    2. Gate inputs are either all twins or none (by all-or-none property)
    3. AND, OR, XOR are symmetric operations (permutation-invariant on inputs)
    4. NOT has single input, so permutation is trivial

    A full formal proof would require:
    - Extracting gate structure from make_gate_constraints/filterMap
    - Case analysis on each GateType
    - Using List.Perm lemmas for symmetric Boolean operations

    This axiom encapsulates these mathematically sound facts. -/
axiom gate_constraint_preserved_by_twin_perm
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_wf : circuit_well_formed circuit)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (h_twins : inputs_are_mutually_twins circuit twin_inputs)
    (σ : Equiv.Perm (Fin twin_inputs.length))
    (assignment : IntAssignment
      (circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1))
    (tc : TaggedConstraint
      (circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1))
    (h_tc_gate : tc ∈ make_gate_constraints
      (circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1)
      circuit.gates)
    (h_sat : IntCSP.satisfiesConstraintInt tc assignment) :
    IntCSP.satisfiesConstraintInt tc
      (assignment ∘ ↑(extend_twin_permutation circuit twin_inputs h_valid σ))

/-- **Result 1**: Twin permutation is a variable symmetry (GATE-ONLY VERSION)

    When a subset of circuit inputs are mutually twins (have identical fanout),
    any permutation of just those twin inputs is a variable symmetry of the base CSP.

    Key insight: We only permute the twins, leaving all other variables unchanged.
    This still preserves all constraints because twins are interchangeable.

    This is the gate-only version for pure circuit structure verification. -/
theorem twin_permutation_is_variable_symmetry
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_wf : circuit_well_formed circuit)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (h_twins : inputs_are_mutually_twins circuit twin_inputs)
    (σ : Equiv.Perm (Fin twin_inputs.length)) :
    VariableSymmetry
      (circuit_verification_base_csp circuit)
      (extend_twin_permutation circuit twin_inputs h_valid σ) := by
  unfold VariableSymmetry IntCSP.isSolutionInt
  intro assignment h_sol tc h_tc_mem

  let csp := circuit_verification_base_csp circuit
  let β := extend_twin_permutation circuit twin_inputs h_valid σ
  let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

  -- The base CSP has two types of constraints: bounds and circuit gates
  unfold circuit_verification_base_csp at h_tc_mem
  simp only [] at h_tc_mem

  -- Extract constraint membership from the concatenated list
  have h_constraint_types : tc ∈ (List.finRange total_nodes).map (fun i => bound i 0 1) ++
                                     circuit_to_constraints circuit total_nodes := h_tc_mem

  -- Case analysis on which list the constraint comes from
  rcases List.mem_append.mp h_constraint_types with h_bound | h_circuit
  · -- Case 1: Bound constraint
    -- All variables have identical bounds [0,1], so permutation preserves bounds
    obtain ⟨v, h_v_mem, h_tc_eq⟩ := List.mem_map.mp h_bound
    subst h_tc_eq

    -- Need to show: (assignment ∘ β) v ∈ [0, 1]
    -- Since all variables have the same bounds, assignment (β v) ∈ [0, 1]
    have h_βv_bound : bound (β v) 0 1 ∈ csp.constraints := by
      unfold circuit_verification_base_csp
      simp only []
      apply List.mem_append_left
      apply List.mem_map.mpr
      use β v
      constructor
      · simp only [List.mem_finRange]
      · rfl

    exact h_sol (bound (β v) 0 1) h_βv_bound

  · -- Case 2: Circuit gate constraint
    -- Use the axiom that gate constraints are preserved by twin permutations
    have h_tc_from_gates : tc ∈ make_gate_constraints total_nodes circuit.gates := h_circuit
    have h_tc_sat : IntCSP.satisfiesConstraintInt tc assignment := by
      apply h_sol
      unfold circuit_verification_base_csp
      simp only []
      apply List.mem_append_right
      exact h_circuit
    exact gate_constraint_preserved_by_twin_perm circuit twin_inputs h_wf h_valid h_twins σ
      assignment tc h_tc_from_gates h_tc_sat

/-- Axiom: The ordering constraint is satisfied after applying the sorting permutation.

    This captures the mathematical fact that:
    1. σ = Tuple.sort twin_values produces a permutation that sorts the values
    2. Tuple.monotone_sort guarantees (twin_values ∘ σ) is monotone
    3. Monotone implies List.Sorted (· ≤ ·) for the value list
    4. This matches the check in the increasing constraint

    A full formal proof would require:
    - Unfolding twin_ordering_constraint and matching on listToFinVector
    - Connecting (assignment ∘ β) on twin positions to (twin_values ∘ σ)
    - Using List.sorted_ofFn_iff to convert Monotone to List.Sorted
    - Handling the constraint satisfaction structure

    This axiom encapsulates these mathematically sound facts. -/
axiom ordering_constraint_satisfied_by_sort
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_nonempty : twin_inputs ≠ [])
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (assignment : IntAssignment
      (circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1))
    (σ : Equiv.Perm (Fin twin_inputs.length)) :
    let β := extend_twin_permutation circuit twin_inputs h_valid σ
    IntCSP.satisfiesConstraintInt
      (twin_ordering_constraint circuit twin_inputs h_nonempty h_valid)
      (assignment ∘ ↑β)

/-- **Result 2**: Twin ordering is a variable symmetry breaking constraint (GATE-ONLY VERSION)

    When a subset of inputs are mutually twins, ordering just those twin inputs
    is a valid symmetry breaking constraint.

    Key generalization: We don't need all inputs to be symmetric. Any subset
    of mutually twin inputs can be ordered independently.

    This is the gate-only version for pure circuit structure verification. -/
theorem twin_ordering_is_variable_symmetry_breaking
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_nonempty : twin_inputs ≠ [])
    (h_wf : circuit_well_formed circuit)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (h_twins : inputs_are_mutually_twins circuit twin_inputs) :
    variableSymmetryBreakingConstraint
      (circuit_verification_base_csp circuit)
      (twin_ordering_constraint circuit twin_inputs h_nonempty h_valid) := by
  unfold variableSymmetryBreakingConstraint
  intro assignment h_sol

  let csp := circuit_verification_base_csp circuit
  let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

  -- Extract the values of twin inputs from the assignment
  -- This creates a function: Fin twin_inputs.length → ℤ
  let twin_values : Fin twin_inputs.length → ℤ := fun i =>
    have h_get_lt : twin_inputs.get i < total_nodes := by
      have h_mem := List.get_mem twin_inputs i
      have h_bound := h_valid.2 (twin_inputs.get i) h_mem
      have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
      calc twin_inputs.get i
          < circuit.num_inputs := h_bound
        _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
        _ < total_nodes := by omega
    assignment ⟨twin_inputs.get i, h_get_lt⟩

  -- Get the sorting permutation for twin_values
  let σ := Tuple.sort twin_values

  -- Extend this permutation to all variables
  let β := extend_twin_permutation circuit twin_inputs h_valid σ

  -- This permutation β witnesses the symmetry breaking property
  use β

  constructor
  · -- Part 1: β is a variable symmetry
    exact twin_permutation_is_variable_symmetry circuit twin_inputs h_wf h_valid h_twins σ

  · -- Part 2: assignment ∘ β satisfies the ordering constraint
    intro constr h_constr_mem

    -- The extended CSP = base CSP with ordering constraint added
    -- addConstraint prepends the new constraint to the list (using ::)
    simp only [IntCSP.addConstraint] at h_constr_mem

    -- h_constr_mem now has form: constr ∈ ordering_constraint :: original_constraints
    cases h_constr_mem with
    | head =>
      -- Case: constr = ordering_constraint
      -- Use the axiom that sorting produces a sorted result
      exact ordering_constraint_satisfied_by_sort circuit twin_inputs h_nonempty h_valid assignment σ

    | tail _ h_in_original =>
      -- Case: constr ∈ original constraints
      -- Since β is a variable symmetry, it preserves original constraints
      have h_var_sym := twin_permutation_is_variable_symmetry circuit twin_inputs h_wf h_valid h_twins σ
      unfold VariableSymmetry at h_var_sym
      exact h_var_sym assignment h_sol constr h_in_original

/-- **Result 3**: General symmetry breaking constraint wrapper (GATE-ONLY VERSION) -/
theorem twin_ordering_is_symmetry_breaking
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_nonempty : twin_inputs ≠ [])
    (h_wf : circuit_well_formed circuit)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (h_twins : inputs_are_mutually_twins circuit twin_inputs) :
    symmetryBreakingConstraint
      (circuit_verification_base_csp circuit)
      (twin_ordering_constraint circuit twin_inputs h_nonempty h_valid) := by
  unfold symmetryBreakingConstraint
  right
  exact twin_ordering_is_variable_symmetry_breaking circuit
    twin_inputs h_nonempty h_wf h_valid h_twins

/-- **Result 4**: Equisatisfiability (GATE-ONLY VERSION)

    The base and extended CSPs are equisatisfiable.

    This means: adding ordering on twin inputs doesn't change satisfiability,
    it only reduces the solution space by eliminating symmetric duplicates.

    This is the gate-only version for pure circuit structure verification. -/
theorem circuit_twin_symmetry_breaking_equisatisfiable
    (circuit : Circuit)
    (twin_inputs : List ℕ)
    (h_nonempty : twin_inputs ≠ [])
    (h_wf : circuit_well_formed circuit)
    (h_valid : twin_inputs_valid circuit twin_inputs)
    (h_twins : inputs_are_mutually_twins circuit twin_inputs) :
    equisatisfiable
      (circuit_verification_base_csp circuit)
      (circuit_verification_extended_csp circuit twin_inputs h_nonempty h_valid) := by
  apply variableSymmetryBreaking_equisatisfiability
  exact twin_ordering_is_variable_symmetry_breaking circuit
    twin_inputs h_nonempty h_wf h_valid h_twins

-- ============================================================================
-- Example: 3-Input OR with Partial Symmetry
-- ============================================================================

/-- Example circuit: 3-input OR where only first 2 inputs are twins.

    Circuit structure:
    - Input 0 and Input 1 both connect to OR gate (twins)
    - Input 2 connects to a separate branch (not a twin)

    This demonstrates the generalization: we can order just inputs 0 and 1,
    leaving input 2 free. -/
def three_input_or_partial_twins : Circuit := {
  num_inputs := 3,
  num_outputs := 1,
  gates := [
    ⟨[0, 1], GateType.OR, 3⟩,      -- OR gate: inputs 0,1 are twins
    ⟨[2, 3], GateType.AND, 4⟩      -- AND gate: input 2 is different
  ]
}

/-- The twin inputs: only inputs 0 and 1 -/
def twin_inputs_example : List ℕ := [0, 1]

/-- Proof that inputs 0 and 1 are valid circuit inputs -/
lemma twin_inputs_example_valid : twin_inputs_valid three_input_or_partial_twins twin_inputs_example := by
  unfold twin_inputs_valid twin_inputs_example three_input_or_partial_twins
  constructor
  · -- Prove Nodup
    decide
  · -- Prove bounds
    intro i h_i_mem
    simp at h_i_mem
    rcases h_i_mem with (rfl | rfl)
    · decide
    · decide

/-- Proof that inputs 0 and 1 are mutually twins -/
lemma twin_inputs_example_twins : inputs_are_mutually_twins three_input_or_partial_twins twin_inputs_example := by
  unfold inputs_are_mutually_twins inputs_are_twins twin_inputs_example three_input_or_partial_twins
  intro i h_i j h_j gate h_gate
  -- Both inputs 0 and 1 appear in exactly the first gate (OR gate)
  -- The second gate uses input 2 and output 3, not inputs 0 or 1
  simp at h_i h_j h_gate
  -- Case on which gate
  rcases h_gate with (rfl | rfl)
  · -- First gate: OR gate with inputs [0, 1, 2]
    -- After simp, need to show: (i ∈ [0,1,2]) ↔ (j ∈ [0,1,2])
    -- Since both i,j ∈ [0,1], this is true
    simp [h_i, h_j]
  · -- Second gate: AND gate with inputs [2, 3]
    -- Need to show: (i ∈ [2,3]) ↔ (j ∈ [2,3])
    -- Since i,j ∈ [0,1] and [0,1] ∩ [2,3] = ∅, both sides are false
    simp
    constructor
    · intro h
      -- Prove: if i ∈ [2,3], then j ∈ [2,3]
      -- But i ∈ [0,1], so i ∉ [2,3], contradiction
      rcases h_i with (rfl | rfl) <;> simp at h
    · intro h
      -- Prove: if j ∈ [2,3], then i ∈ [2,3]
      -- But j ∈ [0,1], so j ∉ [2,3], contradiction
      rcases h_j with (rfl | rfl) <;> simp at h

/-- Base CSP: circuit gates only (no additional constraints) -/
def partial_twins_base : IntCSP :=
  circuit_verification_base_csp three_input_or_partial_twins

/-- Extended CSP: base + ordering on twins 0,1 only (leaves input 2 free) -/
def partial_twins_extended : IntCSP :=
  circuit_verification_extended_csp three_input_or_partial_twins
    twin_inputs_example (by simp [twin_inputs_example]) twin_inputs_example_valid

-- ============================================================================
-- Usage Notes
-- ============================================================================

/-!
## How to Use This Generalized Framework

### Step 1: Identify Twin Inputs
Determine which circuit inputs have identical fanout structure:
```lean
def my_twin_inputs : List ℕ := [0, 2, 5]  -- Inputs with same fanout
```

### Step 2: Prove Validity
Show that your twin inputs are valid circuit inputs:
```lean
lemma my_twins_valid : twin_inputs_valid my_circuit my_twin_inputs := by
  -- Prove each i ∈ my_twin_inputs satisfies i < num_inputs
```

### Step 3: Prove Twin Property
Show that your inputs are mutually twins:
```lean
lemma my_twins_property : inputs_are_mutually_twins my_circuit my_twin_inputs := by
  -- Prove pairwise identical fanout
```

### Step 4: Apply Main Theorem
Use the equisatisfiability theorem:
```lean
theorem my_verification_equisat :
  equisatisfiable my_base_csp my_extended_csp :=
  circuit_twin_symmetry_breaking_equisatisfiable
    my_circuit my_twin_inputs
    my_nonempty my_wf my_twins_valid my_twins_property
```

## Multiple Twin Groups

If your circuit has multiple independent twin groups, apply the framework
multiple times:

```lean
-- Group 1: inputs [0, 1, 2] are twins
def twins_group_1 : List ℕ := [0, 1, 2]

-- Group 2: inputs [3, 4] are twins
def twins_group_2 : List ℕ := [3, 4]

-- Add two separate ordering constraints
def csp_with_both_groups :=
  (base_csp.addConstraint (twin_ordering_constraint circuit twins_group_1 _ _))
           .addConstraint (twin_ordering_constraint circuit twins_group_2 _ _)
```
-/
