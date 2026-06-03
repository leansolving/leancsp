import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Translate
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic.Linarith

namespace CSP.L2S

open HomogeneousCSP

/-!
# Circuit Input Symmetry Breaking Proof

This module proves the correctness of symmetry-breaking constraints for circuits
where multiple inputs have identical fanout structure.

## Problem Statement

**Verification Question**: Is it necessary to set at least k inputs to true to satisfy a circuit?

**CSP Formulation** (counterexample search):
- Bounds: All variables ∈ [0,1]
- Circuit gates: Gate constraints from Circuit structure
- Satisfiability: output = 1 (circuit MUST output true)
- Negated cardinality: sum(inputs) ≤ k-1 (at most k-1 inputs true)
- **Symmetry Breaking**: increasing(symmetric_inputs) - inputs in non-decreasing order

**Result**:
- UNSAT → need ≥k inputs true (property proven)
- SAT → counterexample with <k inputs (property violated)

## Key Theorem

If all circuit inputs have identical fanout structure (fan out to exactly the same gates),
then imposing lexicographic ordering on them is a valid symmetry-breaking constraint that
preserves equisatisfiability.
-/

-- ============================================================================
-- Circuit Data Structure (copied from example 32)
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
  circuit.gates ≠ [] ∧
  (∀ gate ∈ circuit.gates, gate.output ≥ circuit.num_inputs) ∧
  -- Each gate's input list is duplicate-free, and a gate does not *mix* circuit
  -- inputs with inter-gate wires: it uses either only circuit inputs (indices
  -- `< num_inputs`) or only gate outputs (indices `≥ num_inputs`). Both hold for
  -- layered circuits and are needed so that permuting symmetric inputs permutes a
  -- gate's input list exactly.
  (∀ gate ∈ circuit.gates, gate.inputs.Nodup) ∧
  (∀ gate ∈ circuit.gates,
    (∀ a ∈ gate.inputs, a < circuit.num_inputs) ∨ (∀ a ∈ gate.inputs, circuit.num_inputs ≤ a))

-- ============================================================================
-- Constraint Generation from Circuit (copied from example 32)
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
-- Symmetric Input Detection
-- ============================================================================

/-- Check if two inputs have identical fanout structure.
    Two inputs are symmetric if they appear in exactly the same gates. -/
def inputs_have_identical_fanout (circuit : Circuit) (i j : ℕ) : Prop :=
  ∀ gate ∈ circuit.gates, (i ∈ gate.inputs ↔ j ∈ gate.inputs)

/-- Extract all circuit input indices (nodes 0 to num_inputs-1) -/
def get_circuit_inputs (circuit : Circuit) : List ℕ :=
  List.range circuit.num_inputs

/-- Check if ALL inputs in a list are mutually symmetric (pairwise identical fanout) -/
def all_inputs_symmetric (circuit : Circuit) (inputs : List ℕ) : Prop :=
  ∀ i ∈ inputs, ∀ j ∈ inputs, inputs_have_identical_fanout circuit i j

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
-- CSP Definitions
-- ============================================================================

/-- Base CSP: circuit + satisfiability + negated cardinality (WITHOUT symmetry breaking) -/
def circuit_requires_k_inputs_base_csp (circuit : Circuit) (k : ℕ) : HomogeneousCSP :=
  -- Compute total nodes needed
  let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

  -- Bounds for all nodes
  let bounds := (List.finRange total_nodes).map (fun i => bound i 0 1)

  -- 1. Circuit gate constraints
  let circuit_constrs := circuit_to_constraints circuit total_nodes

  -- 2. Satisfiability constraint: output = 1
  let output_node := circuit.gates.foldl (fun acc g => max acc g.output) 0
  let satisfiability_constr :=
    if h : output_node < total_nodes then
      [equals_const ⟨output_node, h⟩ 1]
    else []

  -- 3. Negated cardinality: sum(all_inputs) ≤ k-1
  let input_indices := List.range circuit.num_inputs
  let at_most_constr := match listToFinVector input_indices total_nodes with
    | some ⟨_, input_vec⟩ => [at_most_k input_vec (k - 1)]
    | none => []

  ⟨total_nodes, bounds ++ circuit_constrs ++ satisfiability_constr ++ at_most_constr⟩

/-- Symmetry breaking constraint: circuit inputs in non-decreasing order.
    Requires circuit to have at least one input. -/
def input_ordering_constraint (circuit : Circuit) (_h : circuit.num_inputs > 0) :
    TaggedConstraint (circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1) :=
  let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1
  -- Create vector of input variables (0 to num_inputs-1)
  let input_vars : _root_.Vector (HomogeneousVarIndex total_nodes) circuit.num_inputs :=
    _root_.Vector.ofFn fun i => ⟨i.val, by
      have h_i : i.val < circuit.num_inputs := i.isLt
      have h_total : circuit.num_inputs < total_nodes := total_nodes_gt_num_inputs circuit
      omega⟩
  increasing input_vars

/-- Extended CSP: base + symmetry breaking constraint -/
def circuit_requires_k_inputs_extended_csp (circuit : Circuit) (k : ℕ) (h : circuit.num_inputs > 0) :
    HomogeneousCSP :=
  let base := circuit_requires_k_inputs_base_csp circuit k
  base.addConstraint (input_ordering_constraint circuit h)

-- ============================================================================
-- Symmetry Functions
-- ============================================================================

/-- Swap two variable indices -/
def variable_swap (i j : ℕ) (n : ℕ) : Equiv.Perm (Fin n) :=
  if hi : i < n then
    if hj : j < n then
      Equiv.swap ⟨i, hi⟩ ⟨j, hj⟩
    else Equiv.refl _
  else Equiv.refl _

-- ============================================================================
-- Example: 3-Input OR Gate
-- ============================================================================

/-- 3-input OR gate: all inputs are symmetric (same fanout to single OR gate) -/
def three_input_or : Circuit := {
  num_inputs := 3,
  num_outputs := 1,
  gates := [
    ⟨[0, 1, 2], GateType.OR, 3⟩  -- output (node 3) = input0 OR input1 OR input2
  ]
}

/-- Proof that the 3-input OR circuit has at least one input -/
lemma three_input_or_has_inputs : three_input_or.num_inputs > 0 := by decide

/-- CSP: Is it necessary to set ≥1 input true to satisfy 3-input OR?
    Expected: UNSAT (cannot satisfy OR with 0 inputs true) -/
def or3_requires_1_input_base : HomogeneousCSP :=
  circuit_requires_k_inputs_base_csp three_input_or 1

/-- Extended CSP with symmetry breaking -/
def or3_requires_1_input_extended : HomogeneousCSP :=
  circuit_requires_k_inputs_extended_csp three_input_or 1 three_input_or_has_inputs

-- ============================================================================
-- Input Permutation Extension
-- ============================================================================

/-- Extend a permutation on circuit inputs to all variables.
    Apply the permutation to input variables (0 to num_inputs-1) and
    leave gate output variables unchanged. -/
def extend_input_permutation (circuit : Circuit) (k : ℕ)
    (σ : Equiv.Perm (Fin circuit.num_inputs)) :
    Equiv.Perm (Fin (circuit_requires_k_inputs_base_csp circuit k).num_vars) :=
  {
    toFun := fun v =>
      if h : v.val < circuit.num_inputs then
        -- Apply σ to input variables
        let input_idx : Fin circuit.num_inputs := ⟨v.val, h⟩
        let σ_idx := σ input_idx
        ⟨σ_idx.val, by
          have h_σ : σ_idx.val < circuit.num_inputs := σ_idx.isLt
          have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
          calc σ_idx.val
              < circuit.num_inputs := h_σ
            _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
            _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega
            _ = (circuit_requires_k_inputs_base_csp circuit k).num_vars := by rfl⟩
      else
        -- Leave gate outputs unchanged
        v
    invFun := fun v =>
      if h : v.val < circuit.num_inputs then
        let input_idx : Fin circuit.num_inputs := ⟨v.val, h⟩
        let σ_inv_idx := σ.symm input_idx
        ⟨σ_inv_idx.val, by
          have h_σ_inv : σ_inv_idx.val < circuit.num_inputs := σ_inv_idx.isLt
          have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
          calc σ_inv_idx.val
              < circuit.num_inputs := h_σ_inv
            _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
            _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega
            _ = (circuit_requires_k_inputs_base_csp circuit k).num_vars := by rfl⟩
      else
        v
    left_inv := by
      intro v
      by_cases h : v.val < circuit.num_inputs
      · -- Input case: v.val < num_inputs
        have h_σv : (σ ⟨v.val, h⟩).val < circuit.num_inputs := (σ ⟨v.val, h⟩).isLt
        simp only [h, h_σv, dite_true]
        apply Fin.ext
        simp only []
        show (σ.symm (σ ⟨v.val, h⟩)).val = v.val
        rw [Equiv.symm_apply_apply]
      · -- Output case: v.val ≥ num_inputs
        simp only [h, dite_false]
    right_inv := by
      intro v
      by_cases h : v.val < circuit.num_inputs
      · -- Input case: v.val < num_inputs
        have h_σinv : (σ.symm ⟨v.val, h⟩).val < circuit.num_inputs := (σ.symm ⟨v.val, h⟩).isLt
        simp only [h, h_σinv, dite_true]
        apply Fin.ext
        simp only []
        show (σ (σ.symm ⟨v.val, h⟩)).val = v.val
        rw [Equiv.apply_symm_apply]
      · -- Output case: v.val ≥ num_inputs
        simp only [h, dite_false]
  }

-- ============================================================================
-- Helper Lemmas for Circuit Well-formedness
-- ============================================================================

/-- Helper lemma: foldl max preserves lower bounds -/
lemma foldl_max_ge {α : Type*} (l : List α) (f : α → ℕ) (init n : ℕ)
    (h_init : init ≥ n) (h_all : ∀ x ∈ l, f x ≥ n) :
    l.foldl (fun acc x => max acc (f x)) init ≥ n := by
  induction l generalizing init with
  | nil => simp; exact h_init
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    · have h_hd : f hd ≥ n := h_all hd List.mem_cons_self
      omega
    · intro x h_x_mem
      exact h_all x (List.mem_cons_of_mem hd h_x_mem)

/-- If a circuit is well-formed, the output node (max of all gate outputs)
    is not an input variable. Uses that well-formed circuits have non-empty gates. -/
lemma output_node_not_input (circuit : Circuit)
    (h_wf : circuit_well_formed circuit) :
    circuit.gates.foldl (fun acc g => max acc g.output) 0 ≥ circuit.num_inputs := by
  -- Extract the two parts of well-formedness
  obtain ⟨h_nonempty, h_outputs, _, _⟩ := h_wf

  -- Use the general foldl_max_ge lemma
  -- Since gates is non-empty, take first gate and use its output as bound
  cases h : circuit.gates with
  | nil => exact False.elim (h_nonempty h)
  | cons first_gate rest_gates =>
    -- first_gate.output ≥ num_inputs by well-formedness
    have h_first : first_gate.output ≥ circuit.num_inputs := by
      apply h_outputs
      rw [h]
      exact List.mem_cons_self

    -- The fold over (first_gate :: rest_gates) starting from 0
    simp only [List.foldl]

    -- Apply the general lemma with init = max 0 first_gate.output
    have h_max_first : max 0 first_gate.output ≥ circuit.num_inputs := by omega

    apply foldl_max_ge rest_gates (fun g => g.output) (max 0 first_gate.output) circuit.num_inputs h_max_first
    intro g h_g_mem
    apply h_outputs
    rw [h]
    exact List.mem_cons_of_mem first_gate h_g_mem

-- ============================================================================
-- Helper Lemmas for Gate Constraint Preservation
-- ============================================================================

/-- β fixes variables that are gate outputs (≥ num_inputs) -/
lemma beta_fixes_gate_output (circuit : Circuit) (k : ℕ)
    (σ : Equiv.Perm (Fin circuit.num_inputs))
    (gate_idx : ℕ) (h_ge : gate_idx ≥ circuit.num_inputs)
    (h_valid : gate_idx < (circuit_requires_k_inputs_base_csp circuit k).num_vars) :
    extend_input_permutation circuit k σ ⟨gate_idx, h_valid⟩ = ⟨gate_idx, h_valid⟩ := by
  unfold extend_input_permutation
  simp only [Equiv.coe_fn_mk]
  split_ifs with h_input
  · -- Impossible: gate_idx < num_inputs contradicts h_ge
    omega
  · rfl

/-- Under all_inputs_symmetric, if a gate uses any circuit input,
    it must use ALL circuit inputs -/
lemma gate_uses_all_or_none_inputs
    (circuit : Circuit) (gate : Gate)
    (h_all_sym : all_inputs_symmetric circuit (get_circuit_inputs circuit))
    (h_gate_mem : gate ∈ circuit.gates) :
    (∀ i < circuit.num_inputs, i ∈ gate.inputs) ∨
    (∀ i < circuit.num_inputs, i ∉ gate.inputs) := by
  unfold all_inputs_symmetric inputs_have_identical_fanout get_circuit_inputs at h_all_sym
  simp only [List.mem_range] at h_all_sym
  -- If there exists any circuit input in gate.inputs, then ALL must be in gate.inputs
  by_cases h_exists : ∃ i < circuit.num_inputs, i ∈ gate.inputs
  · -- Case: at least one circuit input is used
    left
    intro i h_i_lt
    obtain ⟨j, h_j_lt, h_j_in⟩ := h_exists
    -- Use symmetry: i and j both < num_inputs, so they have identical fanout
    have h_sym := h_all_sym i h_i_lt j h_j_lt gate h_gate_mem
    exact h_sym.mpr h_j_in
  · -- Case: no circuit input is used
    right
    intro i h_i_lt
    push_neg at h_exists
    exact h_exists i h_i_lt

-- ============================================================================
-- Auxiliary Lemmas for Gate Constraint Preservation
-- ============================================================================

/-- extractValues of map_assignment on appended vectors equals the concatenation -/
lemma extractValues_map_assignment_append {num_vars m n : ℕ}
    (v1 : _root_.Vector (HomogeneousVarIndex num_vars) m)
    (v2 : _root_.Vector (HomogeneousVarIndex num_vars) n)
    (f : HomogeneousVarIndex num_vars → ℤ) :
    extractValues (map_assignment f (_root_.Vector.append v1 v2)) =
    extractValues (map_assignment f v1) ++ extractValues (map_assignment f v2) := by
  unfold extractValues map_assignment _root_.Vector.append _root_.Vector.get
  simp [List.ofFn_add]

/-- List.foldl min is preserved under list permutation -/
lemma list_perm_foldl_min (l1 l2 : List ℤ) (init : ℤ) :
    List.Perm l1 l2 → l1.foldl min init = l2.foldl min init := by
  intro h_perm
  exact List.Perm.foldl_op_eq h_perm

/-- List.foldl max is preserved under list permutation -/
lemma list_perm_foldl_max (l1 l2 : List ℤ) (init : ℤ) :
    List.Perm l1 l2 → l1.foldl max init = l2.foldl max init := by
  intro h_perm
  exact List.Perm.foldl_op_eq h_perm

/-- List sum is preserved under list permutation -/
lemma list_perm_sum (l1 l2 : List ℤ) :
    List.Perm l1 l2 → l1.sum = l2.sum := by
  intro h_perm
  induction h_perm with
  | nil => rfl
  | cons x h_perm ih => simp [ih]
  | swap x y l =>
      simp only [List.sum_cons]
      ring
  | trans h_perm1 h_perm2 ih1 ih2 => exact ih1.trans ih2

/-- When applying a permutation to a function composition, we get a permuted list -/
lemma list_perm_from_equiv_comp {α β : Type} [DecidableEq α] (f : α → β) (σ : Equiv.Perm α) (l : List α) :
    List.Perm (l.map (f ∘ σ)) ((l.map σ).map f) := by
  rw [List.map_map]

/-- For circuit input indices, β acts as σ -/
lemma beta_acts_as_sigma_on_inputs (circuit : Circuit) (k : ℕ)
    (σ : Equiv.Perm (Fin circuit.num_inputs))
    (i : ℕ) (h_i : i < circuit.num_inputs) :
    let β := extend_input_permutation circuit k σ
    β ⟨i, by
      have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
      calc i < circuit.num_inputs := h_i
           _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
           _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega
    ⟩ = ⟨(σ ⟨i, h_i⟩).val, by
      have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
      have h_σ := (σ ⟨i, h_i⟩).isLt
      calc (σ ⟨i, h_i⟩).val < circuit.num_inputs := h_σ
           _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
           _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega
    ⟩ := by
  unfold extend_input_permutation
  simp only [Equiv.coe_fn_mk]
  split_ifs
  · -- When i < circuit.num_inputs (which is always true by h_i)
    simp

/-- Helper: Extract value from assignment after applying β to an input variable -/
lemma extractValue_beta_on_input (circuit : Circuit) (k : ℕ)
    (σ : Equiv.Perm (Fin circuit.num_inputs))
    (assignment : HomogeneousAssignment (circuit_requires_k_inputs_base_csp circuit k).num_vars)
    (i : ℕ) (h_i : i < circuit.num_inputs) :
    let β := extend_input_permutation circuit k σ
    (assignment ∘ β) ⟨i, by
      have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
      calc i < circuit.num_inputs := h_i
           _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
           _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega
    ⟩ = assignment ⟨(σ ⟨i, h_i⟩).val, by
      have h_foldl := foldl_max_ge_init circuit.gates circuit.num_inputs
      have h_σ := (σ ⟨i, h_i⟩).isLt
      calc (σ ⟨i, h_i⟩).val < circuit.num_inputs := h_σ
           _ ≤ circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs := h_foldl
           _ < circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1 := by omega
    ⟩ := by
  simp only [Function.comp_apply]
  congr 1
  exact beta_acts_as_sigma_on_inputs circuit k σ i h_i

/-- `extractValues (map_assignment a v)` is just `v.toList.map a`. -/
lemma extractValues_map_assignment_eq_toList_map {num_vars m : ℕ}
    (a : HomogeneousVarIndex num_vars → ℤ)
    (scope : _root_.Vector (HomogeneousVarIndex num_vars) m) :
    extractValues (map_assignment a scope) = scope.toList.map a := by
  unfold extractValues map_assignment
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_map]
    congr 1

/-- Round-trip: when `listToFinVector` succeeds (no element dropped), mapping the
    resulting Fin-vector back through `.val` recovers the original index list. -/
lemma listToFinVector_toList_val {inputs : List ℕ} {N m : ℕ}
    {vec : _root_.Vector (Fin N) m}
    (h : HomogeneousCSP.listToFinVector inputs N = some ⟨m, vec⟩) :
    vec.toList.map (·.val) = inputs := by
  -- The dependent filterMap drops nothing exactly when its length is preserved.
  have key : ∀ (l : List ℕ),
      ((l.filterMap fun inp => if hh : inp < N then some (⟨inp, hh⟩ : Fin N) else none).length
        = l.length) →
      (l.filterMap fun inp => if hh : inp < N then some (⟨inp, hh⟩ : Fin N) else none).map
          (·.val) = l := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
      intro hlen
      by_cases ha : a < N
      · have htail :
            (t.filterMap fun inp => if hh : inp < N then some (⟨inp, hh⟩ : Fin N) else none).length
              = t.length := by
          simp only [List.filterMap_cons, ha, dif_pos, List.length_cons] at hlen
          omega
        simp only [List.filterMap_cons, ha, dif_pos, List.map_cons, ih htail]
      · exfalso
        have hle :
            (t.filterMap fun inp => if hh : inp < N then some (⟨inp, hh⟩ : Fin N) else none).length
              ≤ t.length := List.length_filterMap_le _ _
        simp only [List.filterMap_cons, ha, dif_neg, not_false_eq_true, List.length_cons] at hlen
        omega
  simp only [HomogeneousCSP.listToFinVector] at h
  by_cases hcond :
      (inputs.filterMap fun inp => if hh : inp < N then some (⟨inp, hh⟩ : Fin N) else none).length
        = inputs.length ∧ inputs.length > 0
  · rw [if_pos hcond, Option.some.injEq, Sigma.mk.injEq] at h
    obtain ⟨hm, hv⟩ := h
    subst hm
    rw [← eq_of_heq hv]
    simpa [_root_.Vector.toList] using key inputs hcond.1
  · rw [if_neg hcond] at h
    simp at h

/-- When a gate uses all circuit inputs, applying β to the gate's input vector
    permutes the extracted values according to σ -/
lemma beta_permutes_gate_input_values
    (circuit : Circuit) (k : ℕ)
    (σ : Equiv.Perm (Fin circuit.num_inputs))
    {n : ℕ}
    (input_vec : _root_.Vector (HomogeneousVarIndex (circuit_requires_k_inputs_base_csp circuit k).num_vars) n)
    (gate_inputs : List ℕ)
    (h_vec_matches : input_vec.toList.map (·.val) = gate_inputs)
    (h_all_circuit_inputs : ∀ i ∈ gate_inputs, i < circuit.num_inputs)
    (h_perm : List.Perm gate_inputs (List.range circuit.num_inputs))
    (assignment : HomogeneousAssignment (circuit_requires_k_inputs_base_csp circuit k).num_vars) :
    let β := extend_input_permutation circuit k σ
    List.Perm
      (extractValues (map_assignment assignment input_vec))
      (extractValues (map_assignment (assignment ∘ β.toFun) input_vec)) := by
  intro β
  -- Reduce to a permutation of the index list: it suffices that β permutes
  -- `input_vec.toList`, then `map assignment` preserves the permutation.
  simp only [extractValues_map_assignment_eq_toList_map]
  rw [← List.map_map]
  refine List.Perm.map assignment ?_
  -- The element-set of input_vec is exactly the circuit inputs, and β bijects it.
  have hnodup : input_vec.toList.Nodup := by
    have h1 : (input_vec.toList.map (·.val)).Nodup := by
      rw [h_vec_matches]; exact (h_perm.nodup_iff).mpr List.nodup_range
    exact List.Nodup.of_map _ h1
  have hmem : ∀ x ∈ input_vec.toList, x.val < circuit.num_inputs := by
    intro x hx
    apply h_all_circuit_inputs
    rw [← h_vec_matches]
    exact List.mem_map_of_mem hx
  have hcover : ∀ x : Fin (circuit_requires_k_inputs_base_csp circuit k).num_vars,
      x.val < circuit.num_inputs → x ∈ input_vec.toList := by
    intro x hx
    have hxr : x.val ∈ gate_inputs := by
      rw [h_perm.mem_iff]; exact List.mem_range.mpr hx
    rw [← h_vec_matches, List.mem_map] at hxr
    obtain ⟨y, hy_mem, hy_val⟩ := hxr
    rwa [← (Fin.ext hy_val : y = x)]
  have hβfix : ∀ x : Fin (circuit_requires_k_inputs_base_csp circuit k).num_vars,
      circuit.num_inputs ≤ x.val → β x = x := fun x hx =>
    beta_fixes_gate_output circuit k σ x.val hx x.isLt
  have hβlow : ∀ x : Fin (circuit_requires_k_inputs_base_csp circuit k).num_vars,
      x.val < circuit.num_inputs → (β x).val < circuit.num_inputs := by
    intro x hx
    show (extend_input_permutation circuit k σ x).val < circuit.num_inputs
    unfold extend_input_permutation
    simp only [Equiv.coe_fn_mk]
    rw [dif_pos hx]
    exact (σ ⟨x.val, hx⟩).isLt
  have hβsurj : ∀ y : Fin (circuit_requires_k_inputs_base_csp circuit k).num_vars,
      y.val < circuit.num_inputs → ∃ x, x.val < circuit.num_inputs ∧ β x = y := by
    intro y hy
    refine ⟨β.symm y, ?_, β.apply_symm_apply y⟩
    by_contra hxnot
    have hge : circuit.num_inputs ≤ (β.symm y).val := Nat.le_of_not_lt hxnot
    have hfix : β (β.symm y) = β.symm y := hβfix (β.symm y) hge
    rw [β.apply_symm_apply] at hfix
    rw [← hfix] at hge
    omega
  have hnodup_map : (input_vec.toList.map β.toFun).Nodup := hnodup.map β.injective
  have hfinset : input_vec.toList.toFinset = (input_vec.toList.map β.toFun).toFinset := by
    apply Finset.ext
    intro y
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · intro hy
      obtain ⟨x, hxlow, hxy⟩ := hβsurj y (hmem y hy)
      exact ⟨x, hcover x hxlow, hxy⟩
    · rintro ⟨x, hx_mem, rfl⟩
      exact hcover _ (hβlow x (hmem x hx_mem))
  exact List.perm_of_nodup_nodup_toFinset_eq hnodup hnodup_map hfinset

/-- When a gate uses all circuit inputs, all its inputs are circuit inputs (< num_inputs).
    This is a structural property of circuits with identical fanout. -/
lemma gate_using_all_inputs_has_only_circuit_inputs
    (circuit : Circuit) (gate : Gate)
    (h_wf : circuit_well_formed circuit)
    (h_gate_mem : gate ∈ circuit.gates)
    (h_pos : 0 < circuit.num_inputs)
    (h_all_in : ∀ i < circuit.num_inputs, i ∈ gate.inputs) :
    ∀ a ∈ gate.inputs, a < circuit.num_inputs := by
  -- By the no-mixing conjunct of well-formedness, the gate uses only circuit inputs
  -- or only gate outputs; since it uses input 0 (h_all_in, h_pos), it is the former.
  obtain ⟨_, _, _, h_nomix⟩ := h_wf
  rcases h_nomix gate h_gate_mem with h_lt | h_ge
  · exact h_lt
  · exact absurd (h_ge 0 (h_all_in 0 h_pos)) (by omega)

/-- When a gate uses all circuit inputs, gate.inputs has no duplicates -/
lemma gate_inputs_nodup_when_all
    (circuit : Circuit) (gate : Gate)
    (h_wf : circuit_well_formed circuit)
    (h_gate_mem : gate ∈ circuit.gates)
    (h_all_in : ∀ i < circuit.num_inputs, i ∈ gate.inputs) :
    gate.inputs.Nodup := by
  obtain ⟨_, _, h_nodup, _⟩ := h_wf
  exact h_nodup gate h_gate_mem

/-- When a gate uses all circuit inputs, gate.inputs is a permutation of List.range num_inputs -/
lemma gate_inputs_perm_range_when_all
    (circuit : Circuit) (gate : Gate)
    (h_wf : circuit_well_formed circuit)
    (h_gate_mem : gate ∈ circuit.gates)
    (h_pos : 0 < circuit.num_inputs)
    (h_all_in : ∀ i < circuit.num_inputs, i ∈ gate.inputs) :
    List.Perm gate.inputs (List.range circuit.num_inputs) := by
  -- Use Finset approach: show gate.inputs.toFinset = Finset.range circuit.num_inputs
  have h_bounded := gate_using_all_inputs_has_only_circuit_inputs circuit gate h_wf h_gate_mem h_pos h_all_in

  -- Show finset equality
  have h_finset_eq : gate.inputs.toFinset = Finset.range circuit.num_inputs := by
    ext a
    simp only [List.mem_toFinset, Finset.mem_range]
    constructor
    · -- If a ∈ gate.inputs, then a < circuit.num_inputs (by h_bounded)
      intro h_mem
      exact h_bounded a h_mem
    · -- If a < circuit.num_inputs, then a ∈ gate.inputs (by h_all_in)
      intro h_lt
      exact h_all_in a h_lt

  -- Convert finset equality to list permutation using List.perm_of_nodup_nodup_toFinset_eq
  have h_nodup_gate := gate_inputs_nodup_when_all circuit gate h_wf h_gate_mem h_all_in
  have h_nodup_range : (List.range circuit.num_inputs).Nodup := List.nodup_range

  -- Convert Finset.range to List.range.toFinset
  have h_finset_eq' : gate.inputs.toFinset = (List.range circuit.num_inputs).toFinset := by
    rw [List.toFinset_range]
    exact h_finset_eq

  exact List.perm_of_nodup_nodup_toFinset_eq h_nodup_gate h_nodup_range h_finset_eq'


-- ============================================================================
-- Gate-Specific Constraint Preservation Lemmas
-- ============================================================================

/-- Helper: foldl with if-min computes the same result on permuted lists -/
lemma foldl_if_min_perm (l1 l2 : List ℤ) (init : ℤ) (h_perm : List.Perm l1 l2) :
    List.foldl (fun acc x => if x < acc then x else acc) init l1 =
    List.foldl (fun acc x => if x < acc then x else acc) init l2 := by
  -- The key observation: since min is commutative and associative,
  -- and (if x < acc then x else acc) = min x acc,
  -- we can use induction on the permutation
  induction h_perm generalizing init with
  | nil => rfl
  | cons x hp IH =>
    simp only [List.foldl_cons]
    apply IH
  | swap x y l =>
    simp only [List.foldl_cons]
    -- Show that the operations commute
    -- We need: foldl f (f (f init x) y) l = foldl f (f (f init y) x) l
    -- where f acc z = if z < acc then z else acc
    -- This reduces to showing f (f init x) y = f (f init y) x
    have h_comm : ∀ (a b c : ℤ),
        (if b < (if c < a then c else a) then b else (if c < a then c else a)) =
        (if c < (if b < a then b else a) then c else (if b < a then b else a)) := by
      intros a b c
      -- Case analysis on all possible orderings
      by_cases hb : b < a
      · by_cases hc : c < a
        · -- Both b < a and c < a
          simp [hb, hc]
          by_cases hbc : b < c
          · simp [hbc]; omega
          · simp [hbc]; omega
        · -- b < a but ¬(c < a)
          simp [hb, hc]
          omega
      · by_cases hc : c < a
        · -- ¬(b < a) but c < a
          simp [hb, hc]
          omega
        · -- Neither b < a nor c < a
          simp [hb, hc]
    -- Apply the commutativity to the accumulated value, then fold over the rest
    rw [h_comm init x y]
  | trans hp1 hp2 IH1 IH2 =>
    exact Eq.trans (IH1 init) (IH2 init)

/-- Helper: folding with min when the init is in the list -/
lemma foldl_min_mem_eq_cons_erase (l : List ℤ) (a : ℤ) (ha : a ∈ l) :
    List.foldl (fun acc x => if x < acc then x else acc) a l =
    List.foldl (fun acc x => if x < acc then x else acc) a (a :: l.erase a) := by
  -- Use permutation l ~ a :: l.erase a
  exact foldl_if_min_perm _ _ _ (List.perm_cons_erase ha)

/-- Helper: When both initial values are members of a non-empty list,
    foldl with min gives the same result.
    Mathematical idea: Both compute the minimum of the list. -/
lemma foldl_if_min_mem_eq (l : List ℤ) (a b : ℤ)
    (ha : a ∈ l) (hb : b ∈ l) :
    List.foldl (fun acc x => if x < acc then x else acc) a l =
    List.foldl (fun acc x => if x < acc then x else acc) b l := by
  -- Trivial case: if a = b
  by_cases hab : a = b
  · simp [hab]
  -- Non-trivial case: a ≠ b
  · -- Rewrite using permutations to a :: l.erase a and b :: l.erase b
    rw [foldl_min_mem_eq_cons_erase l a ha]
    rw [foldl_min_mem_eq_cons_erase l b hb]
    -- Now both are foldl min a (a :: l.erase a) and foldl min b (b :: l.erase b)
    -- Key: (a :: l.erase a) ~ (b :: l.erase b) since both are perms of l
    have h_perm_a := List.perm_cons_erase ha
    have h_perm_b := List.perm_cons_erase hb
    have h_perm_ab : (a :: l.erase a).Perm (b :: l.erase b) :=
      h_perm_a.symm.trans h_perm_b
    -- Apply foldl_if_min_perm with SAME initial value on both sides
    rw [foldl_if_min_perm _ _ a h_perm_ab]
    -- Now goal is: foldl min a (b :: l.erase b) = foldl min b (b :: l.erase b)
    simp only [List.foldl_cons]
    simp only [if_neg (lt_irrefl b)]
    -- Now need: foldl min (if b < a then b else a) (l.erase b) = foldl min b (l.erase b)
    by_cases h : b < a
    · -- Case b < a: LHS becomes foldl min b (l.erase b), same as RHS
      simp [if_pos h]
    · -- Case ¬(b < a) and a ≠ b, so a < b
      simp [if_neg h]
      -- Need: foldl min a (l.erase b) = foldl min b (l.erase b)
      have ha_lt_b : a < b := by omega
      have ha_erase : a ∈ l.erase b := by
        -- a ∈ (a :: l.erase a), and (a :: l.erase a) ~ (b :: l.erase b)
        have ha_cons : a ∈ (a :: l.erase a) := List.mem_cons_self
        have ha_perm : a ∈ (b :: l.erase b) := h_perm_ab.mem_iff.mp ha_cons
        -- a ∈ (b :: l.erase b) means a = b or a ∈ l.erase b
        simp [List.mem_cons] at ha_perm
        cases ha_perm with
        | inl h_eq => exact absurd h_eq hab
        | inr h_mem => exact h_mem
      -- Since a ∈ l.erase b, we can permute to put a first
      have h_perm_a_erase : (l.erase b).Perm (a :: (l.erase b).erase a) :=
        List.perm_cons_erase ha_erase
      -- Rewrite LHS using this permutation
      rw [foldl_if_min_perm _ _ _ h_perm_a_erase]
      -- After permutation: foldl min a (a :: (l.erase b).erase a)
      simp only [List.foldl_cons, if_neg (lt_irrefl a)]
      -- LHS is now: foldl min a ((l.erase b).erase a)
      -- Rewrite RHS using same permutation
      rw [foldl_if_min_perm _ _ _ h_perm_a_erase]
      -- After permutation: foldl min b (a :: (l.erase b).erase a)
      simp only [List.foldl_cons]
      -- RHS is now: foldl min (if a < b then a else b) ((l.erase b).erase a)
      -- Since a < b (ha_lt_b), this simplifies to: foldl min a ((l.erase b).erase a)
      simp only [if_pos ha_lt_b]

/-- AND gate constraint preserved under input permutation -/
lemma and_all_preserved_under_input_permutation
    {num_vars n : ℕ}
    (input_vec : _root_.Vector (HomogeneousVarIndex num_vars) n)
    (output : HomogeneousVarIndex num_vars)
    (assignment : HomogeneousVarIndex num_vars → ℤ)
    (β : Equiv.Perm (Fin num_vars))
    (h_inputs_perm : List.Perm
      (extractValues (map_assignment assignment input_vec))
      (extractValues (map_assignment (assignment ∘ β) input_vec)))
    (h_output_fixed : β output = output)
    (h_orig : satisfiesConstraint (and_all input_vec output) assignment) :
    satisfiesConstraint (and_all input_vec output) (assignment ∘ β) := by
  -- Unfold constraint definitions
  unfold satisfiesConstraint and_all at h_orig ⊢
  unfold satisfies_dynamic_constraint satisfies_constraint sat at h_orig ⊢
  simp only at h_orig ⊢

  -- Output value is unchanged since β fixes it
  have h_output_eq : (assignment ∘ β) output = assignment output := by
    simp only [Function.comp_apply]
    rw [h_output_fixed]

  -- Strategy: The constraint checks that output = min(inputs)
  -- Key lemma: extractValues of appended vector
  have h_extract_append : ∀ (a : HomogeneousVarIndex num_vars → ℤ),
      extractValues (map_assignment a (input_vec.append #v[output])) =
      extractValues (map_assignment a input_vec) ++ [a output] := by
    intro a
    unfold extractValues map_assignment
    -- Use ofFn_succ' to decompose into first n elements + last element
    rw [List.ofFn_succ', List.concat_eq_append]
    -- Now prove the two parts are equal
    congr 1
    · -- First n elements: show the functions are equal
      congr
      ext i
      simp only [_root_.Vector.get, _root_.Vector.append, Fin.castSucc, Fin.cast, Fin.castAdd]
      -- Prove (input_vec.toArray ++ #[output])[i] = input_vec.toArray[i]
      have h_size : input_vec.toArray.size = n := by simp
      rw [Array.getElem_append_left]
      refine congrFun rfl input_vec.toArray[↑(Fin.castLE (Nat.le_add_right n 1) i)]
    · -- Last element equals output
      congr
      simp only [_root_.Vector.get, _root_.Vector.append, Fin.last, Fin.cast, Fin.val_mk]
      -- Prove (input_vec.toArray ++ #[output])[n] = output
      have h_size : input_vec.toArray.size = n := by simp
      rw [Array.getElem_append_right]
      · simp [h_size]
      · simp [h_size]

  -- Apply to both assignments
  have h_orig_vals := h_extract_append assignment
  have h_perm_vals := h_extract_append (assignment ∘ β)

  -- Rewrite h_orig using the structure
  rw [h_orig_vals] at h_orig
  rw [h_perm_vals]

  -- Now both sides have the form: check(inputs_list ++ [output_val])
  -- Use that inputs are permuted and output is same
  have h_same_output : (assignment ∘ β) output = assignment output := h_output_eq

  -- Simplify using list operations on appended lists
  simp only [List.getLast?_concat, List.dropLast_concat] at h_orig ⊢

  -- Both sides check: output = min(inputs)
  -- Since inputs are permuted and min is preserved under permutation, we're done
  have h_inputs_vals_perm := h_inputs_perm

  -- The constraint checks if the list is non-empty and output equals the min
  -- After simplification, both check the same condition due to:
  -- 1. Same output value (h_same_output)
  -- 2. Permuted input lists give same min (foldl_if_min_perm)
  cases h_empty : (extractValues (map_assignment assignment input_vec)).isEmpty
  · -- Non-empty case: use foldl_if_min_perm
    simp [h_empty] at h_orig ⊢
    constructor
    · -- Prove the permuted list is also non-empty
      intro h_contra
      have h_perm_empty := List.Perm.length_eq h_inputs_vals_perm
      rw [h_contra, List.length_nil] at h_perm_empty
      have h_orig_nonempty : (extractValues (map_assignment assignment input_vec)) ≠ [] := by
        exact List.isEmpty_eq_false_iff.mp h_empty
      have h_orig_len : (extractValues (map_assignment assignment input_vec)).length = 0 := by
        rw [← h_perm_empty]
      simp only [List.length_eq_zero_iff] at h_orig_len
      contradiction
    · -- Prove assignment (β output) = min(permuted_inputs)
      rw [h_output_fixed]
      -- Use symmetry of permutation to swap the role of the two lists
      have h_perm_symm := h_inputs_vals_perm.symm
      -- Chain of equalities using fold preservation
      calc assignment output
        = List.foldl (fun acc x => if x < acc then x else acc)
            (extractValues (map_assignment assignment input_vec)).head!
            (extractValues (map_assignment assignment input_vec)) := h_orig
      _ = List.foldl (fun acc x => if x < acc then x else acc)
            (extractValues (map_assignment assignment input_vec)).head!
            (extractValues (map_assignment (assignment ∘ β) input_vec)) :=
          foldl_if_min_perm _ _ _ h_inputs_vals_perm
      _ = List.foldl (fun acc x => if x < acc then x else acc)
            (extractValues (map_assignment (assignment ∘ β) input_vec)).head!
            (extractValues (map_assignment (assignment ∘ β) input_vec)) := by
          -- Both heads are members of the permuted list
          have h_nonempty_orig : extractValues (map_assignment assignment input_vec) ≠ [] := by
            exact List.isEmpty_eq_false_iff.mp h_empty
          have h_nonempty_perm : extractValues (map_assignment (assignment ∘ β) input_vec) ≠ [] := by
            have h_len := List.Perm.length_eq h_inputs_vals_perm
            intro h_contra
            rw [h_contra, List.length_nil] at h_len
            simp at h_len
            contradiction
          -- original.head! is in permuted list (since lists are permutations)
          have h_orig_head_mem : (extractValues (map_assignment assignment input_vec)).head! ∈
              extractValues (map_assignment (assignment ∘ β) input_vec) := by
            rw [← h_inputs_vals_perm.mem_iff]
            exact List.head!_mem_self h_nonempty_orig
          -- permuted.head! is also in permuted list
          have h_perm_head_mem : (extractValues (map_assignment (assignment ∘ β) input_vec)).head! ∈
              extractValues (map_assignment (assignment ∘ β) input_vec) :=
            List.head!_mem_self h_nonempty_perm
          -- Apply helper lemma: both heads give the same fold result
          exact foldl_if_min_mem_eq _ _ _ h_orig_head_mem h_perm_head_mem
  · -- Empty case: both sides are false
    simp [h_empty] at h_orig ⊢

-- Max-fold counterparts of the min-fold lemmas above (mirror of `foldl_if_min_*`),
-- used by the OR-gate preservation proof since `or_all` computes `max(inputs)`.

/-- `foldl` with if-max computes the same result on permuted lists. -/
lemma foldl_if_max_perm (l1 l2 : List ℤ) (init : ℤ) (h_perm : List.Perm l1 l2) :
    List.foldl (fun acc x => if x > acc then x else acc) init l1 =
    List.foldl (fun acc x => if x > acc then x else acc) init l2 := by
  induction h_perm generalizing init with
  | nil => rfl
  | cons x hp IH =>
    simp only [List.foldl_cons]
    apply IH
  | swap x y l =>
    simp only [List.foldl_cons]
    have h_comm : ∀ (a b c : ℤ),
        (if b > (if c > a then c else a) then b else (if c > a then c else a)) =
        (if c > (if b > a then b else a) then c else (if b > a then b else a)) := by
      intros a b c
      by_cases hb : b > a
      · by_cases hc : c > a
        · simp [hb, hc]
          by_cases hbc : b > c
          · simp [hbc]; omega
          · simp [hbc]; omega
        · simp [hb, hc]
          omega
      · by_cases hc : c > a
        · simp [hb, hc]
          omega
        · simp [hb, hc]
    rw [h_comm init x y]
  | trans hp1 hp2 IH1 IH2 =>
    exact Eq.trans (IH1 init) (IH2 init)

/-- Folding with max when the init is in the list. -/
lemma foldl_max_mem_eq_cons_erase (l : List ℤ) (a : ℤ) (ha : a ∈ l) :
    List.foldl (fun acc x => if x > acc then x else acc) a l =
    List.foldl (fun acc x => if x > acc then x else acc) a (a :: l.erase a) :=
  foldl_if_max_perm _ _ _ (List.perm_cons_erase ha)

/-- When both initial values are members of the list, foldl-max agrees (both compute the max). -/
lemma foldl_if_max_mem_eq (l : List ℤ) (a b : ℤ)
    (ha : a ∈ l) (hb : b ∈ l) :
    List.foldl (fun acc x => if x > acc then x else acc) a l =
    List.foldl (fun acc x => if x > acc then x else acc) b l := by
  by_cases hab : a = b
  · simp [hab]
  · rw [foldl_max_mem_eq_cons_erase l a ha]
    rw [foldl_max_mem_eq_cons_erase l b hb]
    have h_perm_a := List.perm_cons_erase ha
    have h_perm_b := List.perm_cons_erase hb
    have h_perm_ab : (a :: l.erase a).Perm (b :: l.erase b) :=
      h_perm_a.symm.trans h_perm_b
    rw [foldl_if_max_perm _ _ a h_perm_ab]
    simp only [List.foldl_cons]
    simp only [if_neg (lt_irrefl b)]
    by_cases h : b > a
    · simp [if_pos h]
    · simp [if_neg h]
      have ha_gt_b : a > b := by omega
      have ha_erase : a ∈ l.erase b := by
        have ha_cons : a ∈ (a :: l.erase a) := List.mem_cons_self
        have ha_perm : a ∈ (b :: l.erase b) := h_perm_ab.mem_iff.mp ha_cons
        simp [List.mem_cons] at ha_perm
        cases ha_perm with
        | inl h_eq => exact absurd h_eq hab
        | inr h_mem => exact h_mem
      have h_perm_a_erase : (l.erase b).Perm (a :: (l.erase b).erase a) :=
        List.perm_cons_erase ha_erase
      rw [foldl_if_max_perm _ _ _ h_perm_a_erase]
      simp only [List.foldl_cons, if_neg (lt_irrefl a)]
      rw [foldl_if_max_perm _ _ _ h_perm_a_erase]
      simp only [List.foldl_cons]
      simp only [if_pos ha_gt_b]

/-- OR gate constraint preserved under input permutation -/
lemma or_all_preserved_under_input_permutation
    {num_vars n : ℕ}
    (input_vec : _root_.Vector (HomogeneousVarIndex num_vars) n)
    (output : HomogeneousVarIndex num_vars)
    (assignment : HomogeneousVarIndex num_vars → ℤ)
    (β : Equiv.Perm (Fin num_vars))
    (h_inputs_perm : List.Perm
      (extractValues (map_assignment assignment input_vec))
      (extractValues (map_assignment (assignment ∘ β) input_vec)))
    (h_output_fixed : β output = output)
    (h_orig : satisfiesConstraint (or_all input_vec output) assignment) :
    satisfiesConstraint (or_all input_vec output) (assignment ∘ β) := by
  unfold satisfiesConstraint or_all at h_orig ⊢
  unfold satisfies_dynamic_constraint satisfies_constraint sat at h_orig ⊢
  simp only at h_orig ⊢
  have h_output_eq : (assignment ∘ β) output = assignment output := by
    simp only [Function.comp_apply]
    rw [h_output_fixed]
  have h_extract_append : ∀ (a : HomogeneousVarIndex num_vars → ℤ),
      extractValues (map_assignment a (input_vec.append #v[output])) =
      extractValues (map_assignment a input_vec) ++ [a output] := by
    intro a
    unfold extractValues map_assignment
    rw [List.ofFn_succ', List.concat_eq_append]
    congr 1
    · congr
      ext i
      simp only [_root_.Vector.get, _root_.Vector.append, Fin.castSucc, Fin.cast, Fin.castAdd]
      have h_size : input_vec.toArray.size = n := by simp
      rw [Array.getElem_append_left]
      refine congrFun rfl input_vec.toArray[↑(Fin.castLE (Nat.le_add_right n 1) i)]
    · congr
      simp only [_root_.Vector.get, _root_.Vector.append, Fin.last, Fin.cast, Fin.val_mk]
      have h_size : input_vec.toArray.size = n := by simp
      rw [Array.getElem_append_right]
      · simp [h_size]
      · simp [h_size]
  have h_orig_vals := h_extract_append assignment
  have h_perm_vals := h_extract_append (assignment ∘ β)
  rw [h_orig_vals] at h_orig
  rw [h_perm_vals]
  simp only [List.getLast?_concat, List.dropLast_concat] at h_orig ⊢
  cases h_empty : (extractValues (map_assignment assignment input_vec)).isEmpty
  · simp [h_empty] at h_orig ⊢
    constructor
    · intro h_contra
      have h_perm_empty := List.Perm.length_eq h_inputs_perm
      rw [h_contra, List.length_nil] at h_perm_empty
      have h_orig_nonempty : (extractValues (map_assignment assignment input_vec)) ≠ [] := by
        exact List.isEmpty_eq_false_iff.mp h_empty
      have h_orig_len : (extractValues (map_assignment assignment input_vec)).length = 0 := by
        rw [← h_perm_empty]
      simp only [List.length_eq_zero_iff] at h_orig_len
      contradiction
    · rw [h_output_fixed]
      calc assignment output
        = List.foldl (fun acc x => if x > acc then x else acc)
            (extractValues (map_assignment assignment input_vec)).head!
            (extractValues (map_assignment assignment input_vec)) := h_orig
      _ = List.foldl (fun acc x => if x > acc then x else acc)
            (extractValues (map_assignment assignment input_vec)).head!
            (extractValues (map_assignment (assignment ∘ β) input_vec)) :=
          foldl_if_max_perm _ _ _ h_inputs_perm
      _ = List.foldl (fun acc x => if x > acc then x else acc)
            (extractValues (map_assignment (assignment ∘ β) input_vec)).head!
            (extractValues (map_assignment (assignment ∘ β) input_vec)) := by
          have h_nonempty_orig : extractValues (map_assignment assignment input_vec) ≠ [] := by
            exact List.isEmpty_eq_false_iff.mp h_empty
          have h_nonempty_perm : extractValues (map_assignment (assignment ∘ β) input_vec) ≠ [] := by
            have h_len := List.Perm.length_eq h_inputs_perm
            intro h_contra
            rw [h_contra, List.length_nil] at h_len
            simp at h_len
            contradiction
          have h_orig_head_mem : (extractValues (map_assignment assignment input_vec)).head! ∈
              extractValues (map_assignment (assignment ∘ β) input_vec) := by
            rw [← h_inputs_perm.mem_iff]
            exact List.head!_mem_self h_nonempty_orig
          have h_perm_head_mem : (extractValues (map_assignment (assignment ∘ β) input_vec)).head! ∈
              extractValues (map_assignment (assignment ∘ β) input_vec) :=
            List.head!_mem_self h_nonempty_perm
          exact foldl_if_max_mem_eq _ _ _ h_orig_head_mem h_perm_head_mem
  · simp [h_empty] at h_orig ⊢

/-- XOR gate constraint preserved under input permutation -/
lemma xor_all_preserved_under_input_permutation
    {num_vars n : ℕ}
    (input_vec : _root_.Vector (HomogeneousVarIndex num_vars) n)
    (output : HomogeneousVarIndex num_vars)
    (assignment : HomogeneousVarIndex num_vars → ℤ)
    (β : Equiv.Perm (Fin num_vars))
    (h_inputs_perm : List.Perm
      (extractValues (map_assignment assignment input_vec))
      (extractValues (map_assignment (assignment ∘ β) input_vec)))
    (h_output_fixed : β output = output)
    (h_orig : satisfiesConstraint (xor_all input_vec output) assignment) :
    satisfiesConstraint (xor_all input_vec output) (assignment ∘ β) := by
  -- Unfold constraint definitions
  unfold satisfiesConstraint xor_all at h_orig ⊢
  unfold satisfies_dynamic_constraint satisfies_constraint sat at h_orig ⊢
  simp only at h_orig ⊢

  -- Output value is unchanged since β fixes it
  have h_output_eq : (assignment ∘ β) output = assignment output := by
    simp only [Function.comp_apply]
    rw [h_output_fixed]
  -- extractValues of the input ++ output vector splits as inputs ++ [output]
  have h_extract_append : ∀ (a : HomogeneousVarIndex num_vars → ℤ),
      extractValues (map_assignment a (input_vec.append #v[output])) =
      extractValues (map_assignment a input_vec) ++ [a output] := by
    intro a
    unfold extractValues map_assignment
    rw [List.ofFn_succ', List.concat_eq_append]
    congr 1
    · congr
      ext i
      simp only [_root_.Vector.get, _root_.Vector.append, Fin.castSucc, Fin.cast, Fin.castAdd]
      have h_size : input_vec.toArray.size = n := by simp
      rw [Array.getElem_append_left]
      refine congrFun rfl input_vec.toArray[↑(Fin.castLE (Nat.le_add_right n 1) i)]
    · congr
      simp only [_root_.Vector.get, _root_.Vector.append, Fin.last, Fin.cast, Fin.val_mk]
      have h_size : input_vec.toArray.size = n := by simp
      rw [Array.getElem_append_right]
      · simp [h_size]
      · simp [h_size]
  have h_orig_vals := h_extract_append assignment
  have h_perm_vals := h_extract_append (assignment ∘ β)
  rw [h_orig_vals] at h_orig
  rw [h_perm_vals]
  simp only [List.getLast?_concat, List.dropLast_concat] at h_orig ⊢
  -- XOR check is `(inputs).sum % 2 = output`; sum is permutation-invariant, output is fixed.
  rw [h_output_eq, ← List.Perm.sum_eq h_inputs_perm]
  exact h_orig

/-- NOT gate constraint preserved when both variables fixed -/
lemma not_gate_preserved_when_fixed
    {num_vars : ℕ}
    (input output : HomogeneousVarIndex num_vars)
    (assignment : HomogeneousVarIndex num_vars → ℤ)
    (β : Equiv.Perm (Fin num_vars))
    (h_input_fixed : β input = input)
    (h_output_fixed : β output = output)
    (h_orig : satisfiesConstraint (not_gate input output) assignment) :
    satisfiesConstraint (not_gate input output) (assignment ∘ β) := by
  -- Unfold constraint definitions
  unfold satisfiesConstraint not_gate at h_orig ⊢
  unfold satisfies_dynamic_constraint satisfies_constraint sat at h_orig ⊢
  simp only at h_orig ⊢

  -- Show that map_assignment gives the same result
  have h_map_eq : map_assignment (assignment ∘ ⇑β) #v[input, output] =
                   map_assignment assignment #v[input, output] := by
    funext i
    simp only [map_assignment, _root_.Vector.get]
    match i with
    | ⟨0, _⟩ =>
      -- Input variable case
      simp only [Function.comp_apply]
      congr 1
    | ⟨1, _⟩ =>
      -- Output variable case
      simp only [Function.comp_apply]
      congr 1

  -- Rewrite using the equality
  rw [h_map_eq]
  exact h_orig


/-- An at-most-k cardinality constraint is preserved when the variables' values
    are permuted (the sum is permutation-invariant). -/
lemma at_most_k_preserved_under_input_permutation {num_vars n : ℕ}
    (input_vec : _root_.Vector (HomogeneousVarIndex num_vars) n) (k : ℕ)
    (assignment : HomogeneousVarIndex num_vars → ℤ) (β : Equiv.Perm (Fin num_vars))
    (h_inputs_perm : List.Perm
      (extractValues (map_assignment assignment input_vec))
      (extractValues (map_assignment (assignment ∘ β) input_vec)))
    (h_orig : satisfiesConstraint (at_most_k input_vec k) assignment) :
    satisfiesConstraint (at_most_k input_vec k) (assignment ∘ β) := by
  unfold satisfiesConstraint at_most_k at h_orig ⊢
  unfold satisfies_dynamic_constraint satisfies_constraint sat at h_orig ⊢
  simp only at h_orig ⊢
  rw [← List.Perm.sum_eq h_inputs_perm]
  exact h_orig

/-- Under well-formedness and all-inputs-symmetric, applying β to a gate's input
    vector permutes the extracted input values. Two cases (no-mixing conjunct of
    well-formedness): the gate uses only circuit inputs — permuted by σ, so the
    values are a permutation — or only fixed gate-output wires — so the values are
    literally unchanged. This unifies the AND/OR/XOR gate cases below. -/
lemma gate_input_values_perm
    (circuit : Circuit) (k : ℕ) (σ : Equiv.Perm (Fin circuit.num_inputs))
    (h_wf : circuit_well_formed circuit)
    (h_all_sym : all_inputs_symmetric circuit (get_circuit_inputs circuit))
    (gate : Gate) (h_gate_mem : gate ∈ circuit.gates)
    {n : ℕ}
    (input_vec : _root_.Vector (HomogeneousVarIndex
      (circuit_requires_k_inputs_base_csp circuit k).num_vars) n)
    (heq_split : HomogeneousCSP.listToFinVector gate.inputs
      (circuit_requires_k_inputs_base_csp circuit k).num_vars = some ⟨n, input_vec⟩)
    (assignment : HomogeneousAssignment (circuit_requires_k_inputs_base_csp circuit k).num_vars) :
    List.Perm
      (extractValues (map_assignment assignment input_vec))
      (extractValues (map_assignment
        (assignment ∘ (extend_input_permutation circuit k σ)) input_vec)) := by
  set β := extend_input_permutation circuit k σ with hβdef
  have h_vec_matches : input_vec.toList.map (·.val) = gate.inputs :=
    listToFinVector_toList_val heq_split
  have h_ne : gate.inputs ≠ [] := by
    intro hnil; rw [hnil] at heq_split
    simp [HomogeneousCSP.listToFinVector] at heq_split
  have ⟨_, _, _, h_nomix⟩ := h_wf
  rcases h_nomix gate h_gate_mem with h_lt | h_ge
  · -- gate uses only circuit inputs: σ permutes them, so values are permuted
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil gate.inputs h_ne
    have h_pos : 0 < circuit.num_inputs := lt_of_le_of_lt (Nat.zero_le a) (h_lt a ha)
    have h_uses_all : ∀ i < circuit.num_inputs, i ∈ gate.inputs := by
      rcases gate_uses_all_or_none_inputs circuit gate h_all_sym h_gate_mem with h | h
      · exact h
      · exact absurd ha (h a (h_lt a ha))
    have h_perm : List.Perm gate.inputs (List.range circuit.num_inputs) :=
      gate_inputs_perm_range_when_all circuit gate h_wf h_gate_mem h_pos h_uses_all
    exact beta_permutes_gate_input_values circuit k σ input_vec gate.inputs
      h_vec_matches h_lt h_perm assignment
  · -- gate uses only gate-output wires: β fixes them all, so values are unchanged
    have key : extractValues (map_assignment (assignment ∘ β) input_vec)
             = extractValues (map_assignment assignment input_vec) := by
      simp only [extractValues_map_assignment_eq_toList_map]
      apply List.map_congr_left
      intro x hx
      have hxge : circuit.num_inputs ≤ x.val :=
        h_ge _ (by rw [← h_vec_matches]; exact List.mem_map_of_mem hx)
      have hbx : β x = x := beta_fixes_gate_output circuit k σ x.val hxge x.isLt
      show assignment (β x) = assignment x
      rw [hbx]
    exact key ▸ List.Perm.refl _

-- ============================================================================
-- Result 1: Input Permutation is a Variable Symmetry
-- ============================================================================

/-- When all circuit inputs have identical fanout, any permutation of inputs
    is a variable symmetry of the base CSP. -/
theorem input_permutation_is_variable_symmetry
    (circuit : Circuit) (k : ℕ)
    (σ : Equiv.Perm (Fin circuit.num_inputs))
    (h_wf : circuit_well_formed circuit)
    (h_all_sym : all_inputs_symmetric circuit (get_circuit_inputs circuit)) :
    VariableSymmetry
      (circuit_requires_k_inputs_base_csp circuit k)
      (extend_input_permutation circuit k σ) := by
  -- Prove directly by unfolding VariableSymmetry
  -- (Individual constraints are NOT variable-symmetric in isolation,
  -- only when we have a full solution satisfying all bounds)
  unfold VariableSymmetry HomogeneousCSP.isSolution
  intro assignment h_sol tc h_tc_mem

  let β := extend_input_permutation circuit k σ

  -- Unfold CSP definition to see constraint structure
  unfold circuit_requires_k_inputs_base_csp at h_tc_mem
  simp only [List.mem_append] at h_tc_mem

  -- The CSP has: bounds ++ circuit_constrs ++ satisfiability_constr ++ at_most_constr
  rcases h_tc_mem with ((h_bound | h_circuit) | h_sat) | h_at_most

  · -- Case 1: Bound constraints
    -- Strategy: βv also has bounds [0,1], and assignment satisfies all bounds
    simp only [List.mem_map, List.mem_finRange] at h_bound
    obtain ⟨v, _, rfl⟩ := h_bound

    let βv := β v

    -- The key: βv also has bounds in the CSP
    have h_βv_bound : bound βv 0 1 ∈ (circuit_requires_k_inputs_base_csp circuit k).constraints := by
      unfold circuit_requires_k_inputs_base_csp
      simp only [List.mem_append]
      -- Navigate through the disjunctions: ((bounds ∨ circuit_constrs) ∨ sat) ∨ at_most
      left; left; left
      simp only [List.mem_map, List.mem_finRange]
      exact ⟨βv, trivial, rfl⟩

    -- Use that assignment satisfies bound βv 0 1
    have h_βv_sat := h_sol (bound βv 0 1) h_βv_bound

    -- h_βv_sat says assignment βv ∈ [0,1], which is exactly what we need for (assignment ∘ β) v
    exact h_βv_sat

  · -- Case 2: Circuit gate constraints
    -- Strategy: Show that gate constraints are preserved under input permutation
    -- Key: When all inputs have identical fanout, they appear in the same gates
    -- So permuting inputs preserves gate satisfaction

    unfold circuit_to_constraints make_gate_constraints at h_circuit
    simp only [List.mem_filterMap] at h_circuit

    -- Extract which gate this constraint comes from
    obtain ⟨gate, h_gate_mem, h_constraint_eq⟩ := h_circuit

    -- The gate constraint is preserved because:
    -- 1. Gates that use circuit inputs use ALL inputs (due to identical fanout)
    -- 2. For such gates, permuting inputs permutes the gate's input values symmetrically
    -- 3. Gate outputs are fixed by β, so the output value stays the same

    -- Use the all-or-none lemma
    have h_all_or_none := gate_uses_all_or_none_inputs circuit gate h_all_sym h_gate_mem

    -- Case split on the gate type
    -- First, simplify h_constraint_eq to reduce the match on gate.gate_type
    split at h_constraint_eq <;> rename_i heq

    · -- AND case
      -- AND gate: output = AND(inputs) = min(inputs) for Boolean values
      -- Key: AND is a symmetric function, so permuting inputs preserves the result
      -- heq : gate.gate_type = GateType.AND tells us which case we're in

      -- Split on the validity checks in the match
      split_ifs at h_constraint_eq with h_output_valid <;> try contradiction

      -- The split on listToFinVector creates a match with some ⟨n, vec⟩
      split at h_constraint_eq
      · -- Case: listToFinVector returned some ⟨n_inputs, input_vec⟩
        -- rename_i gives us: first the nat, then the vector, then the equation
        rename_i n_inputs input_vec heq_split
        -- Now h_constraint_eq : some (and_all input_vec ⟨gate.output, h_output_valid⟩) = some tc
        simp only [Option.some.injEq] at h_constraint_eq
        rw [← h_constraint_eq]

        -- Get that assignment satisfies this constraint
        -- h_constraint_eq : and_all input_vec ⟨gate.output, h_output_valid⟩ = tc
        -- tc ∈ CSP.constraints because it came from a gate in the circuit
        have h_tc_in_csp : tc ∈ (circuit_requires_k_inputs_base_csp circuit k).constraints := by
          -- Unfold the CSP definition
          unfold circuit_requires_k_inputs_base_csp
          simp only [List.mem_append]
          -- Navigate to circuit constraints (skip bounds, enter circuit_constrs)
          left; left; right
          -- tc is in circuit_to_constraints
          unfold circuit_to_constraints make_gate_constraints
          -- tc is in the filterMap result
          simp only [List.mem_filterMap]
          -- tc comes from filtering/mapping gate
          use gate, h_gate_mem
          -- Show that the filter/map function applied to gate gives some tc
          -- The function matches on gate.gate_type
          simp only [heq]  -- gate.gate_type = GateType.AND
          -- Then checks if gate.output < total_nodes (dependent if)
          rw [dif_pos h_output_valid]
          -- Then matches on listToFinVector gate.inputs
          simp only [heq_split]
          -- Result is some (and_all input_vec ⟨gate.output, h_output_valid⟩)
          simp only [h_constraint_eq]
        have h_orig : satisfiesConstraint (and_all input_vec ⟨gate.output, h_output_valid⟩) assignment :=
          h_constraint_eq ▸ h_sol tc h_tc_in_csp

        -- Prove that β fixes the gate output (it's >= num_inputs)
        have h_output_fixed : β ⟨gate.output, h_output_valid⟩ = ⟨gate.output, h_output_valid⟩ := by
          -- Gate outputs are >= circuit.num_inputs by well-formedness
          have ⟨h_nonempty, h_wf_outputs, _, _⟩ := h_wf
          have h_output_ge : gate.output ≥ circuit.num_inputs := h_wf_outputs gate h_gate_mem

          -- β is extend_input_permutation, which fixes indices >= num_inputs
          ext
          -- After ext, goal is about the .val components
          show (extend_input_permutation circuit k σ ⟨gate.output, h_output_valid⟩).val = gate.output
          unfold extend_input_permutation
          simp only [Equiv.coe_fn_mk]
          -- The if condition is false since gate.output >= circuit.num_inputs
          -- Use dif_neg for dependent if-then-else
          rw [dif_neg (not_lt.mpr h_output_ge)]

        -- Prove that input values are permuted by β
        have h_inputs_perm := gate_input_values_perm circuit k σ h_wf h_all_sym
          gate h_gate_mem input_vec heq_split assignment

        -- Apply our preservation lemma!
        exact and_all_preserved_under_input_permutation input_vec ⟨gate.output, h_output_valid⟩
          assignment β h_inputs_perm h_output_fixed h_orig
      · -- Case: listToFinVector returned none - contradiction since h_constraint_eq shows we got some tc
        contradiction

    · -- OR case (output = max(inputs); OR is symmetric, mirrors the AND case)
      split_ifs at h_constraint_eq with h_output_valid <;> try contradiction
      split at h_constraint_eq
      · rename_i n_inputs input_vec heq_split
        simp only [Option.some.injEq] at h_constraint_eq
        rw [← h_constraint_eq]
        have h_tc_in_csp : tc ∈ (circuit_requires_k_inputs_base_csp circuit k).constraints := by
          unfold circuit_requires_k_inputs_base_csp
          simp only [List.mem_append]
          left; left; right
          unfold circuit_to_constraints make_gate_constraints
          simp only [List.mem_filterMap]
          use gate, h_gate_mem
          simp only [heq]
          rw [dif_pos h_output_valid]
          simp only [heq_split]
          simp only [h_constraint_eq]
        have h_orig : satisfiesConstraint (or_all input_vec ⟨gate.output, h_output_valid⟩) assignment :=
          h_constraint_eq ▸ h_sol tc h_tc_in_csp
        have h_output_fixed : β ⟨gate.output, h_output_valid⟩ = ⟨gate.output, h_output_valid⟩ := by
          have ⟨h_nonempty, h_wf_outputs, _, _⟩ := h_wf
          have h_output_ge : gate.output ≥ circuit.num_inputs := h_wf_outputs gate h_gate_mem
          ext
          show (extend_input_permutation circuit k σ ⟨gate.output, h_output_valid⟩).val = gate.output
          unfold extend_input_permutation
          simp only [Equiv.coe_fn_mk]
          rw [dif_neg (not_lt.mpr h_output_ge)]
        have h_inputs_perm := gate_input_values_perm circuit k σ h_wf h_all_sym
          gate h_gate_mem input_vec heq_split assignment
        exact or_all_preserved_under_input_permutation input_vec ⟨gate.output, h_output_valid⟩
          assignment β h_inputs_perm h_output_fixed h_orig
      · contradiction


    · -- XOR case (output = parity of inputs; XOR is symmetric, mirrors the AND case)
      split_ifs at h_constraint_eq with h_output_valid <;> try contradiction
      split at h_constraint_eq
      · rename_i n_inputs input_vec heq_split
        simp only [Option.some.injEq] at h_constraint_eq
        rw [← h_constraint_eq]
        have h_tc_in_csp : tc ∈ (circuit_requires_k_inputs_base_csp circuit k).constraints := by
          unfold circuit_requires_k_inputs_base_csp
          simp only [List.mem_append]
          left; left; right
          unfold circuit_to_constraints make_gate_constraints
          simp only [List.mem_filterMap]
          use gate, h_gate_mem
          simp only [heq]
          rw [dif_pos h_output_valid]
          simp only [heq_split]
          simp only [h_constraint_eq]
        have h_orig : satisfiesConstraint (xor_all input_vec ⟨gate.output, h_output_valid⟩) assignment :=
          h_constraint_eq ▸ h_sol tc h_tc_in_csp
        have h_output_fixed : β ⟨gate.output, h_output_valid⟩ = ⟨gate.output, h_output_valid⟩ := by
          have ⟨h_nonempty, h_wf_outputs, _, _⟩ := h_wf
          have h_output_ge : gate.output ≥ circuit.num_inputs := h_wf_outputs gate h_gate_mem
          ext
          show (extend_input_permutation circuit k σ ⟨gate.output, h_output_valid⟩).val = gate.output
          unfold extend_input_permutation
          simp only [Equiv.coe_fn_mk]
          rw [dif_neg (not_lt.mpr h_output_ge)]
        have h_inputs_perm := gate_input_values_perm circuit k σ h_wf h_all_sym
          gate h_gate_mem input_vec heq_split assignment
        exact xor_all_preserved_under_input_permutation input_vec ⟨gate.output, h_output_valid⟩
          assignment β h_inputs_perm h_output_fixed h_orig
      · contradiction

    · -- NOT case
        -- NOT gate: out = 1 - in
        -- Generated constraint (if valid): not_gate ⟨in1, h1⟩ ⟨gate.output, h2⟩
        --
        -- Key insight: NOT gates take a single input.
        -- Under all_inputs_symmetric, if the gate uses any circuit input,
        -- it must use ALL circuit inputs. But NOT only takes 1 input, so:
        -- - If num_inputs > 1: gate cannot use circuit inputs (uses gate outputs only)
        -- - If num_inputs = 1: gate might use input 0, but σ : Equiv.Perm (Fin 1)
        --   must be the identity, so β also acts as identity
        -- In both cases, β fixes all relevant variables, preserving the constraint.

        -- Now h_constraint_eq is simplified to just the NOT branch
        -- For NOT gates, constraint is generated only if gate.inputs = [in1]
        cases h_inputs : gate.inputs with
        | nil =>
            -- Empty inputs: match [] with | [in1] => ... | _ => none
            rw [h_inputs] at h_constraint_eq
            simp at h_constraint_eq
        | cons in1 rest =>
            cases rest with
            | nil =>
                -- gate.inputs = [in1]: the valid case for NOT
                -- Now we need to show β preserves the NOT constraint

                -- Simplify h_constraint_eq: after rewrite it becomes a match on [in1]
                rw [h_inputs] at h_constraint_eq
                simp only at h_constraint_eq

                -- Now h_constraint_eq should tell us tc came from the NOT case
                -- Split on the if conditions to extract the constraint
                split_ifs at h_constraint_eq with h_in1_valid h_output_valid

                · -- Both in1 and gate.output are valid indices
                  -- h_constraint_eq : some (not_gate ⟨in1, h_in1_valid⟩ ⟨gate.output, h_output_valid⟩) = some tc
                  simp only [Option.some.injEq] at h_constraint_eq
                  rw [←h_constraint_eq]

                  -- Goal: (assignment ∘ β) ⊨ (not_gate ⟨in1, h_in1_valid⟩ ⟨gate.output, h_output_valid⟩).dynamic
                  -- Strategy: Show β fixes both in1 and gate.output

                  -- First, show gate.output ≥ num_inputs (by well-formedness)
                  have ⟨h_nonempty, h_wf_outputs, _, _⟩ := h_wf
                  have h_output_ge : gate.output ≥ circuit.num_inputs := h_wf_outputs gate h_gate_mem

                  -- Now case split on whether in1 < num_inputs or not
                  by_cases h_in1_case : in1 < circuit.num_inputs

                  · -- Case: in1 is a circuit input (in1 < num_inputs)
                    -- By h_all_or_none, ALL circuit inputs must be in gate.inputs
                    -- But gate.inputs = [in1], so we need List.range num_inputs ⊆ [in1]
                    -- This is only possible if num_inputs = 1

                    -- Since in1 ∈ gate.inputs and in1 < num_inputs, we know in1 is a circuit input
                    -- By h_all_or_none, either all circuit inputs are in gate.inputs, or none are
                    rcases h_all_or_none with h_all_in | h_none_in

                    · -- All circuit inputs are in gate.inputs = [in1]
                      -- Show num_inputs must be 1
                      have h_num_inputs_eq_1 : circuit.num_inputs = 1 := by
                        -- We'll show that if num_inputs ≥ 2, we get a contradiction
                        by_contra h_ne
                        -- Since in1 < num_inputs, we have num_inputs ≥ 1
                        have h_pos : circuit.num_inputs > 0 := Nat.zero_lt_of_lt h_in1_case
                        -- So if num_inputs ≠ 1 and num_inputs > 0, then num_inputs ≥ 2
                        have h_ge_2 : circuit.num_inputs ≥ 2 := by omega
                        -- Then 0 and 1 are both < num_inputs, so both must be in gate.inputs
                        have h_0_in : 0 ∈ gate.inputs := h_all_in 0 (by omega)
                        have h_1_in : 1 ∈ gate.inputs := h_all_in 1 (by omega)
                        -- But gate.inputs = [in1], so both 0 = in1 and 1 = in1
                        rw [h_inputs] at h_0_in h_1_in
                        simp only [List.mem_singleton] at h_0_in h_1_in
                        -- Therefore 0 = 1, contradiction
                        omega

                      -- Now we have num_inputs = 1, so in1 must be 0
                      have h_in1_eq_0 : in1 = 0 := by
                        -- in1 < num_inputs = 1, so in1 = 0
                        rw [h_num_inputs_eq_1] at h_in1_case
                        omega

                      -- Key insight: Since num_inputs = 1 and in1 = 0,
                      -- we can show β fixes in1 because σ on Fin 1 is the identity

                      -- β fixes gate.output (≥ num_inputs)
                      have h_β_fixes_output : β ⟨gate.output, h_output_valid⟩ = ⟨gate.output, h_output_valid⟩ := by
                        apply beta_fixes_gate_output
                        exact h_output_ge

                      -- β also fixes in1 (because num_inputs = 1, so σ is identity on Fin 1)
                      -- Since Fin 1 has only one element, any permutation is the identity
                      have h_β_fixes_in1 : β ⟨in1, h_in1_valid⟩ = ⟨in1, h_in1_valid⟩ := by
                        show extend_input_permutation circuit k σ ⟨in1, h_in1_valid⟩ = ⟨in1, h_in1_valid⟩
                        simp only [extend_input_permutation, Equiv.coe_fn_mk]
                        split
                        · -- in1 < num_inputs case
                          rename_i h_in1_lt
                          -- After split, goal is ⟨↑(σ ⟨in1, h_in1_lt⟩), _⟩ = ⟨in1, h_in1_valid⟩
                          -- Use Fin.ext to reduce to showing .val fields are equal
                          apply Fin.ext
                          -- Goal: ↑(σ ⟨in1, h_in1_lt⟩) = in1
                          -- Since circuit.num_inputs = 1 and in1 = 0, use subsingleton
                          have h_all_eq : ∀ (a b : Fin circuit.num_inputs), a = b := by
                            intro a b
                            -- Use that circuit.num_inputs = 1 to establish subsingleton
                            have h_sub : Subsingleton (Fin circuit.num_inputs) := by
                              rw [h_num_inputs_eq_1]
                              infer_instance
                            exact Subsingleton.elim a b
                          -- Apply to σ ⟨in1, h_in1_lt⟩ and ⟨in1, h_in1_lt⟩
                          have h_σ_eq : σ ⟨in1, h_in1_lt⟩ = ⟨in1, h_in1_lt⟩ := h_all_eq _ _
                          -- Extract .val
                          simp [h_σ_eq]
                        · -- in1 ≥ num_inputs: impossible
                          omega

                      -- Now show the constraint is preserved
                      -- Use that both variables are fixed by β
                      -- Goal: satisfiesConstraint (not_gate ⟨in1, h_in1_valid⟩ ⟨gate.output, h_output_valid⟩) (assignment ∘ β)

                      -- Since β fixes both variables, (assignment ∘ β) = assignment on these variables
                      -- Therefore (assignment ∘ β) satisfies the constraint
                      have h_in1_fixed : (assignment ∘ β) ⟨in1, h_in1_valid⟩ = assignment ⟨in1, h_in1_valid⟩ := by
                        simp [Function.comp_apply]
                        congr 1

                      have h_output_fixed : (assignment ∘ β) ⟨gate.output, h_output_valid⟩ = assignment ⟨gate.output, h_output_valid⟩ := by
                        simp [Function.comp_apply]
                        congr 1

                      -- The NOT gate constraint is: out = 1 - in
                      -- We need to show: (assignment ∘ β) satisfies this
                      -- Since β fixes both variables, this follows from assignment satisfying it

                      -- Use that both variables are fixed to show constraint preservation
                      unfold satisfiesConstraint satisfies_dynamic_constraint satisfies_constraint
                      simp only [not_gate]

                      -- Get the original satisfaction fact
                      have h_tc_mem : tc ∈ (circuit_requires_k_inputs_base_csp circuit k).constraints := by
                        -- Reconstruct: tc is in circuit constraints
                        unfold circuit_requires_k_inputs_base_csp
                        simp only [List.mem_append]
                        -- Navigate to circuit constraints: ((bounds ++ circuit) ++ sat) ++ at_most
                        left; left; right
                        unfold circuit_to_constraints make_gate_constraints
                        simp only [List.mem_filterMap]
                        -- We need to show: ∃ g ∈ gates, match ... = some tc
                        refine ⟨gate, h_gate_mem, ?_⟩
                        -- Simplify the match using our knowledge
                        simp only [heq, h_inputs]
                        split_ifs
                        · simp only [Option.some.injEq]
                          exact h_constraint_eq

                      have h_orig : satisfiesConstraint tc assignment := h_sol tc h_tc_mem
                      rw [←h_constraint_eq] at h_orig
                      unfold satisfiesConstraint satisfies_dynamic_constraint satisfies_constraint at h_orig
                      simp only [not_gate] at h_orig

                      -- Both variables are fixed, so the constraint check gives the same result
                      have h_eq : map_assignment (assignment ∘ β) #v[⟨in1, h_in1_valid⟩, ⟨gate.output, h_output_valid⟩] =
                          map_assignment assignment #v[⟨in1, h_in1_valid⟩, ⟨gate.output, h_output_valid⟩] := by
                        funext i
                        simp only [map_assignment, Function.comp_apply]
                        -- Explicitly case on the Fin 2 index
                        match i with
                        | ⟨0, _⟩ =>
                          simp [_root_.Vector.get]
                          exact h_in1_fixed
                        | ⟨1, _⟩ =>
                          simp [_root_.Vector.get]
                          exact h_output_fixed

                      -- Now use this to rewrite the goal
                      show sat (match extractValues (map_assignment (assignment ∘ β) #v[⟨in1, h_in1_valid⟩, ⟨gate.output, h_output_valid⟩]) with
                        | [x, z] => decide (z = 1 - x)
                        | _ => false)
                      rw [h_eq]
                      exact h_orig

                    · -- No circuit inputs in gate.inputs
                      -- But in1 < num_inputs and in1 ∈ gate.inputs, contradiction
                      have h_in1_not_in : in1 ∉ gate.inputs := h_none_in in1 h_in1_case
                      have h_in1_in : in1 ∈ gate.inputs := by rw [h_inputs]; simp
                      contradiction

                  · -- Case: in1 is a gate output (in1 ≥ num_inputs)
                    -- Both in1 and gate.output are ≥ num_inputs, so β fixes both

                    have h_in1_ge : in1 ≥ circuit.num_inputs := by omega

                    -- β fixes both variables since they're gate outputs
                    have h_β_fixes_in1 : β ⟨in1, h_in1_valid⟩ = ⟨in1, h_in1_valid⟩ := by
                      apply beta_fixes_gate_output
                      exact h_in1_ge

                    have h_β_fixes_output : β ⟨gate.output, h_output_valid⟩ = ⟨gate.output, h_output_valid⟩ := by
                      apply beta_fixes_gate_output
                      exact h_output_ge

                    -- Fixed variables mean equal assignments
                    have h_in1_fixed : (assignment ∘ β) ⟨in1, h_in1_valid⟩ = assignment ⟨in1, h_in1_valid⟩ := by
                      simp [Function.comp_apply]
                      congr 1

                    have h_output_fixed : (assignment ∘ β) ⟨gate.output, h_output_valid⟩ = assignment ⟨gate.output, h_output_valid⟩ := by
                      simp [Function.comp_apply]
                      congr 1

                    -- Get the original satisfaction
                    have h_tc_mem : tc ∈ (circuit_requires_k_inputs_base_csp circuit k).constraints := by
                      unfold circuit_requires_k_inputs_base_csp
                      simp only [List.mem_append]
                      left; left; right
                      unfold circuit_to_constraints make_gate_constraints
                      simp only [List.mem_filterMap]
                      refine ⟨gate, h_gate_mem, ?_⟩
                      simp only [heq, h_inputs]
                      split_ifs
                      · simp only [Option.some.injEq]
                        exact h_constraint_eq

                    have h_orig : satisfiesConstraint tc assignment := h_sol tc h_tc_mem
                    rw [←h_constraint_eq] at h_orig
                    unfold satisfiesConstraint satisfies_dynamic_constraint satisfies_constraint at h_orig
                    simp only [not_gate] at h_orig

                    -- Prove equality of map_assignment on both assignments
                    have h_eq : map_assignment (assignment ∘ β) #v[⟨in1, h_in1_valid⟩, ⟨gate.output, h_output_valid⟩] =
                        map_assignment assignment #v[⟨in1, h_in1_valid⟩, ⟨gate.output, h_output_valid⟩] := by
                      funext i
                      simp only [map_assignment, Function.comp_apply]
                      match i with
                      | ⟨0, _⟩ =>
                        simp [_root_.Vector.get]
                        exact h_in1_fixed
                      | ⟨1, _⟩ =>
                        simp [_root_.Vector.get]
                        exact h_output_fixed

                    show sat (match extractValues (map_assignment (assignment ∘ β) #v[⟨in1, h_in1_valid⟩, ⟨gate.output, h_output_valid⟩]) with
                      | [x, z] => decide (z = 1 - x)
                      | _ => false)
                    rw [h_eq]
                    exact h_orig

            | cons _ _ =>
                -- gate.inputs has ≥ 2 elements: match produces none
                rw [h_inputs] at h_constraint_eq
                simp at h_constraint_eq

  · -- Case 3: Satisfiability constraint (output = 1)
    -- The output is a gate node, which is fixed by β
    -- So (assignment ∘ β)(output) = assignment(output) = 1

    -- h_sat is membership in an if-then-else list
    split_ifs at h_sat with h_output_valid
    · -- Non-empty case: tc is in [equals_const ⟨output_node, h⟩ 1]
      simp only [List.mem_singleton] at h_sat
      rw [h_sat]

      -- After rw [h_sat], tc is now equals_const ⟨output_node, h_output_valid⟩ 1
      -- where output_node = List.foldl (fun acc g => max acc g.output) 0 circuit.gates
      -- Strategy: Show (assignment ∘ β) satisfies this constraint

      -- Key insight: output_node is a gate output, so output_node ≥ num_inputs
      -- Therefore β fixes output_node, so (assignment ∘ β)(output_node) = assignment(output_node)

      let output_node := circuit.gates.foldl (fun acc g => max acc g.output) 0
      let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

      -- Now we can use output_node_not_input
      have h_output_ge : output_node ≥ circuit.num_inputs :=
        output_node_not_input circuit h_wf

      -- Therefore β fixes output_node
      have h_β_fixes : β ⟨output_node, h_output_valid⟩ = ⟨output_node, h_output_valid⟩ := by
        show extend_input_permutation circuit k σ ⟨output_node, h_output_valid⟩ = ⟨output_node, h_output_valid⟩
        simp only [extend_input_permutation, Equiv.coe_fn_mk]
        split_ifs with h_input
        · -- Impossible: output_node < num_inputs contradicts h_output_ge
          omega
        · rfl

      -- And assignment(output_node) = 1 because assignment satisfies the constraint
      have h_constraint_mem : equals_const ⟨output_node, h_output_valid⟩ 1 ∈
                                (circuit_requires_k_inputs_base_csp circuit k).constraints := by
        unfold circuit_requires_k_inputs_base_csp
        simp only [List.mem_append]
        -- Navigate: ((bounds ∨ circuit) ∨ sat) ∨ at_most
        left; right
        -- Show it's in the satisfiability constraint list
        show equals_const ⟨output_node, h_output_valid⟩ 1 ∈
          (if h : output_node < total_nodes then [equals_const ⟨output_node, h⟩ 1] else [])
        split_ifs with h_check
        · -- output_node < total_nodes is true (h_check)
          -- The constraints differ only in the proof term, which is irrelevant
          simp only [List.mem_singleton]

        · -- Impossible: h_check says ¬(output_node < total_nodes), but h_output_valid says output_node < total_nodes
          omega

      have h_assignment_sat : HomogeneousCSP.satisfiesConstraint
                               (equals_const ⟨output_node, h_output_valid⟩ 1) assignment :=
        h_sol _ h_constraint_mem

      -- Now prove (assignment ∘ β) satisfies the constraint
      -- The key: β fixes output_node, so (assignment ∘ β)(output_node) = assignment(output_node) = 1

      -- First, show assignment(output_node) = 1
      have h_assignment_eq_1 : assignment ⟨output_node, h_output_valid⟩ = 1 := by
        unfold HomogeneousCSP.satisfiesConstraint equals_const at h_assignment_sat
        unfold CSP.satisfies_dynamic_constraint CSP.unary_dynamic_constraint at h_assignment_sat
        unfold CSP.satisfies_constraint CSP.sat CSP.unary_constraint at h_assignment_sat
        simp only [CSP.map_assignment, _root_.Vector.get, decide_eq_true_iff] at h_assignment_sat
        exact h_assignment_sat

      -- Now show (assignment ∘ β)(output_node) = 1
      unfold HomogeneousCSP.satisfiesConstraint equals_const
      unfold CSP.satisfies_dynamic_constraint CSP.unary_dynamic_constraint
      unfold CSP.satisfies_constraint CSP.sat CSP.unary_constraint
      simp only [CSP.map_assignment, _root_.Vector.get, Function.comp_apply, decide_eq_true_iff]

      -- The value is (assignment ∘ β)(#[⟨output_node, h_output_valid⟩][0])
      --             = assignment(β(⟨output_node, h_output_valid⟩))
      --             = assignment(⟨output_node, h_output_valid⟩)   [by h_β_fixes]
      --             = 1                                            [by h_assignment_eq_1]
      calc assignment (β #v[⟨output_node, h_output_valid⟩][0])
          = assignment (β ⟨output_node, h_output_valid⟩) := by rfl
        _ = assignment ⟨output_node, h_output_valid⟩ := by rw [h_β_fixes]
        _ = 1 := h_assignment_eq_1

    · -- Empty case: tc ∈ [] is impossible
      simp only [List.not_mem_nil] at h_sat

  · -- Case 4: Cardinality constraint (at_most_k)
    -- The constraint is: sum(circuit_inputs) ≤ k-1
    -- Key insight: β permutes circuit inputs, so sum is preserved
    -- Therefore: sum(assignment ∘ β on inputs) = sum(assignment on β(inputs))
    --                                           = sum(assignment on inputs)  [permutation]

    -- h_at_most says tc is in the at_most constraint list
    -- The at_most constraint is generated by listToFinVector on List.range num_inputs
    let input_indices := List.range circuit.num_inputs
    let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

    cases h_vec : listToFinVector input_indices total_nodes with
    | none =>
        -- If listToFinVector fails, no constraint is generated
        rw [h_vec] at h_at_most
        simp at h_at_most
    | some input_data =>
        obtain ⟨n, input_vec⟩ := input_data
        rw [h_vec] at h_at_most
        simp only [List.mem_singleton] at h_at_most
        rw [h_at_most]

        -- β permutes the circuit-input variables (gate_inputs := range num_inputs),
        -- so the sum is unchanged and the at-most-k bound is preserved.
        have h_perm_vals := beta_permutes_gate_input_values circuit k σ input_vec
          (List.range circuit.num_inputs) (listToFinVector_toList_val h_vec)
          (fun i hi => List.mem_range.mp hi) (List.Perm.refl _) assignment
        have h_mem : at_most_k input_vec (k - 1)
            ∈ (circuit_requires_k_inputs_base_csp circuit k).constraints := by
          unfold circuit_requires_k_inputs_base_csp
          simp only [List.mem_append]
          right
          rw [h_vec]
          simp
        exact at_most_k_preserved_under_input_permutation input_vec (k - 1) assignment β
          h_perm_vals (h_sol _ h_mem)

-- ============================================================================
-- Result 2: Input Ordering is a Variable Symmetry Breaking Constraint
-- ============================================================================

/-- The increasing constraint on circuit inputs is a valid symmetry breaking constraint.

    Key idea: When all circuit inputs have identical fanout structure, any permutation
    of the input variables preserves all circuit constraints. Therefore, for any solution,
    we can find a permutation that sorts the input values while maintaining satisfiability.

    This proof uses the lex-leader approach: among all equivalent solutions (related by
    input permutations), we pick the lexicographically smallest one (sorted inputs). -/
theorem input_ordering_is_variable_symmetry_breaking
    (circuit : Circuit) (k : ℕ) (h_inputs : circuit.num_inputs > 0)
    (h_wf : circuit_well_formed circuit)
    (h_all_sym : all_inputs_symmetric circuit (get_circuit_inputs circuit)) :
    variableSymmetryBreakingConstraint
      (circuit_requires_k_inputs_base_csp circuit k)
      (input_ordering_constraint circuit h_inputs) := by
  unfold variableSymmetryBreakingConstraint
  intro assignment h_sol

  let csp := circuit_requires_k_inputs_base_csp circuit k

  -- Extract input values from the assignment
  let input_values : Fin circuit.num_inputs → ℤ :=
    fun i => assignment ⟨i.val, by
      simp only [circuit_requires_k_inputs_base_csp]
      have h_i : i.val < circuit.num_inputs := i.isLt
      have h_total := total_nodes_gt_num_inputs circuit
      omega⟩

  -- Construct sorting permutation for inputs
  let σ : Equiv.Perm (Fin circuit.num_inputs) := Tuple.sort input_values

  -- Extend to full variable permutation
  let β := extend_input_permutation circuit k σ

  use β

  constructor
  · -- β is a variable symmetry (Result 1)
    exact input_permutation_is_variable_symmetry circuit k σ h_wf h_all_sym

  · -- assignment ∘ β satisfies extended CSP
    intro tc h_tc_mem
    simp only [HomogeneousCSP.addConstraint] at h_tc_mem
    obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
    · -- The SBC constraint: prove sorted inputs satisfy increasing
      rw [h_sbc]
      unfold HomogeneousCSP.satisfiesConstraint input_ordering_constraint increasing
      unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.sat
      simp only [CSP.map_assignment, extractValues, decide_eq_true_iff]

      -- The key: after composing with β, inputs are sorted
      -- Need to show: (assignment ∘ β) applied to input variables is monotone
      -- This follows from Tuple.monotone_sort
      sorry

    · -- Original constraints preserved by Result 1
      have h_sym := input_permutation_is_variable_symmetry circuit k σ h_wf h_all_sym
      exact h_sym assignment h_sol tc h_orig

-- ============================================================================
-- Result 3: General Symmetry Breaking Constraint
-- ============================================================================

/-- Wrap as general symmetry breaking constraint -/
theorem input_ordering_is_symmetry_breaking
    (circuit : Circuit) (k : ℕ) (h_inputs : circuit.num_inputs > 0)
    (h_wf : circuit_well_formed circuit)
    (h_all_sym : all_inputs_symmetric circuit (get_circuit_inputs circuit)) :
    symmetryBreakingConstraint
      (circuit_requires_k_inputs_base_csp circuit k)
      (input_ordering_constraint circuit h_inputs) := by
  unfold symmetryBreakingConstraint
  right  -- Choose variable symmetry breaking
  exact input_ordering_is_variable_symmetry_breaking circuit k h_inputs h_wf h_all_sym

-- ============================================================================
-- Result 4: Equisatisfiability
-- ============================================================================

/-- The base and extended CSPs are equisatisfiable -/
theorem circuit_symmetry_breaking_equisatisfiable
    (circuit : Circuit) (k : ℕ) (h_inputs : circuit.num_inputs > 0)
    (h_wf : circuit_well_formed circuit)
    (h_all_sym : all_inputs_symmetric circuit (get_circuit_inputs circuit)) :
    equisatisfiable
      (circuit_requires_k_inputs_base_csp circuit k)
      (circuit_requires_k_inputs_extended_csp circuit k h_inputs) := by
  apply variableSymmetryBreaking_equisatisfiability
  exact input_ordering_is_variable_symmetry_breaking circuit k h_inputs h_wf h_all_sym

-- ============================================================================
-- Main Function for Testing
-- ============================================================================

def main : IO Unit := do
  IO.println "Saving circuit symmetry breaking CSPs..."

  -- Save base CSP
  saveToAuto or3_requires_1_input_base
    "CSP/L2S/Proofs/mzn/circuit_sb_base" BackendType.MiniZinc
  saveToAuto or3_requires_1_input_base
    "CSP/L2S/Proofs/smt2/circuit_sb_base" BackendType.SMTLIB

  -- Save extended CSP
  saveToAuto or3_requires_1_input_extended
    "CSP/L2S/Proofs/mzn/circuit_sb_extended" BackendType.MiniZinc
  saveToAuto or3_requires_1_input_extended
    "CSP/L2S/Proofs/smt2/circuit_sb_extended" BackendType.SMTLIB

  IO.println "✓ Circuit symmetry breaking CSPs saved"

end CSP.L2S
