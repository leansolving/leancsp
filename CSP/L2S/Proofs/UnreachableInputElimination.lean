import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith

namespace CSP.L2S

open HomogeneousCSP

/-!
# Unreachable Input Elimination

This module proves that circuit inputs which do not reach any output can be
safely fixed to any value (e.g., 0) without affecting satisfiability.

## Problem Statement

Given a Boolean circuit where input `i` has no path to any output node,
the circuit's satisfiability is independent of the value assigned to `i`.

## Key Theorem

If `¬reaches_output circuit i`, then:
- Any solution with `assignment i = v` has a corresponding solution with `assignment i = 0`
- The base and modified CSPs are equisatisfiable

## Extension Path

This infrastructure (reachability, independence) can later be extended to:
- **Parity-based pure literal elimination**: Track NOT/XOR parity along paths
- **Monotone input optimization**: Inputs with even parity can be set to 1

## Proof Strategy

1. Define reachability via transitive closure of gate connections
2. Prove the "Coincidence Lemma": unreachable inputs don't affect node values
3. Use strong induction on node indices (DAG structure ensures termination)
4. Conclude satisfiability independence
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
  output_nodes : List ℕ    -- Explicit list of output node IDs
  deriving Repr

-- ============================================================================
-- Reachability Definitions
-- ============================================================================

/-- Direct dependency: node `src` feeds into node `tgt` via some gate.
    This defines the edges of the circuit DAG. -/
def DirectDependency (c : Circuit) (src tgt : ℕ) : Prop :=
  ∃ g ∈ c.gates, src ∈ g.inputs ∧ g.output = tgt

/-- Transitive reachability: there exists a path from `src` to `tgt`
    through the circuit's gate connections.
    Uses Mathlib's TransGen (non-reflexive transitive closure). -/
def Reaches (c : Circuit) (src tgt : ℕ) : Prop :=
  Relation.TransGen (DirectDependency c) src tgt

/-- Reflexive-transitive reachability: `src` can reach `tgt` in zero or more steps. -/
def ReachesOrEq (c : Circuit) (src tgt : ℕ) : Prop :=
  src = tgt ∨ Reaches c src tgt

/-- A node is an output node if it's in the circuit's output list. -/
def is_output (c : Circuit) (node : ℕ) : Prop :=
  node ∈ c.output_nodes

/-- Input `i` reaches some output: there exists an output node reachable from `i`. -/
def reaches_output (c : Circuit) (i : ℕ) : Prop :=
  ∃ out, is_output c out ∧ ReachesOrEq c i out

-- ============================================================================
-- Well-Formedness: Strict Topological Order
-- ============================================================================

/-- A circuit is strictly ordered if all gate inputs are strictly less than
    the gate output. This ensures the circuit is a DAG and enables strong
    induction on node indices. -/
def circuit_strictly_ordered (c : Circuit) : Prop :=
  ∀ g ∈ c.gates, ∀ inp ∈ g.inputs, inp < g.output

/-- Basic well-formedness: gates exist and outputs are disjoint from inputs. -/
def circuit_well_formed (c : Circuit) : Prop :=
  c.gates ≠ [] ∧ ∀ g ∈ c.gates, g.output ≥ c.num_inputs

/-- Combined well-formedness for our proofs. -/
def circuit_valid (c : Circuit) : Prop :=
  circuit_well_formed c ∧ circuit_strictly_ordered c

-- ============================================================================
-- Circuit Evaluation (Semantics)
-- ============================================================================

/-- Compute the total number of nodes in the circuit. -/
def total_nodes (c : Circuit) : ℕ :=
  c.gates.foldl (fun acc g => max acc g.output) c.num_inputs + 1

/-- Find the gate (if any) that outputs to node `v`. -/
def find_gate_for_output (c : Circuit) (v : ℕ) : Option Gate :=
  c.gates.find? (fun g => g.output = v)

/-- Helper: extract that g.output = v from find_gate_for_output result -/
lemma find_gate_output_eq (c : Circuit) (v : ℕ) (g : Gate)
    (h : find_gate_for_output c v = some g) : g.output = v := by
  unfold find_gate_for_output at h
  have := List.find?_some h
  simp only [decide_eq_true_eq] at this
  exact this

/-- Helper: extract that g ∈ c.gates from find_gate_for_output result -/
lemma find_gate_mem (c : Circuit) (v : ℕ) (g : Gate)
    (h : find_gate_for_output c v = some g) : g ∈ c.gates := by
  unfold find_gate_for_output at h
  exact List.mem_of_find?_eq_some h

/-- Evaluate a Boolean operation on a list of Boolean inputs. -/
def eval_gate_op (gt : GateType) (inputs : List Bool) : Bool :=
  match gt with
  | GateType.AND => inputs.all id
  | GateType.OR  => inputs.any id
  | GateType.XOR => inputs.foldl xor false
  | GateType.NOT => match inputs with
                    | [b] => !b
                    | _ => false  -- malformed NOT gate

/-- Evaluate a node's value given an assignment to input nodes.
    Uses a fuel parameter to ensure termination.
    For a valid circuit with max node index M, fuel = M + 1 suffices. -/
def eval_node_fuel (c : Circuit) (assignment : ℕ → Bool) (fuel : ℕ) (v : ℕ) : Bool :=
  match fuel with
  | 0 => false  -- Out of fuel (shouldn't happen for valid circuits)
  | fuel' + 1 =>
    if v < c.num_inputs then
      assignment v
    else
      match find_gate_for_output c v with
      | none => false  -- No gate outputs to v
      | some g =>
          let input_vals := g.inputs.map (eval_node_fuel c assignment fuel')
          eval_gate_op g.gate_type input_vals

/-- Evaluate a node with sufficient fuel (total_nodes). -/
def eval_node (c : Circuit) (assignment : ℕ → Bool) (v : ℕ) : Bool :=
  eval_node_fuel c assignment (total_nodes c) v

/-- Circuit satisfaction: all output nodes evaluate to true. -/
def circuit_satisfied (c : Circuit) (assignment : ℕ → Bool) : Prop :=
  ∀ out ∈ c.output_nodes, eval_node c assignment out = true

-- ============================================================================
-- Helper Lemmas for Reachability
-- ============================================================================

/-- If there's a direct dependency from src to tgt, then src reaches tgt. -/
lemma reaches_of_direct (c : Circuit) (src tgt : ℕ)
    (h : DirectDependency c src tgt) : Reaches c src tgt :=
  Relation.TransGen.single h

/-- Transitivity of Reaches. -/
lemma reaches_trans (c : Circuit) (a b d : ℕ)
    (hab : Reaches c a b) (hbc : Reaches c b d) : Reaches c a d :=
  Relation.TransGen.trans hab hbc

/-- If src reaches tgt, and there's a direct edge from tgt to next,
    then src reaches next. -/
lemma reaches_step (c : Circuit) (src tgt next : ℕ)
    (h_reach : Reaches c src tgt) (h_edge : DirectDependency c tgt next) :
    Reaches c src next :=
  Relation.TransGen.tail h_reach h_edge

/-- If there's an edge from u to v, and u is reachable from src,
    then v is reachable from src. -/
lemma reaches_extend (c : Circuit) (src u v : ℕ)
    (h_reach : ReachesOrEq c src u) (h_edge : DirectDependency c u v) :
    Reaches c src v := by
  cases h_reach with
  | inl h_eq =>
    subst h_eq
    exact Relation.TransGen.single h_edge
  | inr h_trans =>
    exact Relation.TransGen.tail h_trans h_edge

-- ============================================================================
-- The Coincidence Lemma (with fuel)
-- ============================================================================

/-- Key lemma: If input `i` does not reach node `v`, then the value at `v`
    is independent of the assignment to `i`.

    This version uses fuel for termination and induction. -/
theorem value_independent_of_unreachable_fuel
    (c : Circuit)
    (_h_strict : circuit_strictly_ordered c)
    (i : ℕ) (_h_i_input : i < c.num_inputs)
    (fuel : ℕ) (v : ℕ)
    (h_no_reach : ¬ReachesOrEq c i v) :
    ∀ assignment : ℕ → Bool,
      eval_node_fuel c (Function.update assignment i true) fuel v =
      eval_node_fuel c (Function.update assignment i false) fuel v := by
  induction fuel generalizing v with
  | zero =>
    intro assignment
    simp [eval_node_fuel]
  | succ fuel' ih =>
    intro assignment
    simp only [eval_node_fuel]
    -- Case 1: v is an input node
    by_cases h_v_input : v < c.num_inputs
    · simp only [h_v_input, ↓reduceIte]
      -- Since ¬ReachesOrEq c i v, we have i ≠ v
      have h_neq : i ≠ v := by
        intro h_eq
        apply h_no_reach
        left
        exact h_eq
      -- Function.update doesn't change value at v when i ≠ v
      have h_neq' : v ≠ i := Ne.symm h_neq
      rw [Function.update_apply, Function.update_apply]
      simp only [h_neq', ↓reduceIte]
    · -- Case 2: v is a gate output
      simp only [h_v_input, ↓reduceIte]
      -- Find the gate outputting v
      cases h_gate : find_gate_for_output c v with
      | none => rfl  -- No gate, both sides are false
      | some g =>
        simp only []
        congr 1
        -- Need to show the input values are the same
        apply List.map_eq_map_iff.mpr
        intro u h_u_in
        -- Show that i does not reach u (otherwise i would reach v)
        have h_no_reach_u : ¬ReachesOrEq c i u := by
          intro h_reach_u
          apply h_no_reach
          -- If i reaches u, and u → v is an edge, then i reaches v
          have h_edge : DirectDependency c u v := by
            use g
            constructor
            · exact find_gate_mem c v g h_gate
            · constructor
              · exact h_u_in
              · exact find_gate_output_eq c v g h_gate
          right
          exact reaches_extend c i u v h_reach_u h_edge
        exact ih u h_no_reach_u assignment

/-- Main coincidence lemma using eval_node. -/
theorem value_independent_of_unreachable
    (c : Circuit)
    (h_valid : circuit_valid c)
    (i : ℕ) (h_i_input : i < c.num_inputs)
    (v : ℕ)
    (h_no_reach : ¬ReachesOrEq c i v) :
    ∀ assignment : ℕ → Bool,
      eval_node c (Function.update assignment i true) v =
      eval_node c (Function.update assignment i false) v := by
  unfold eval_node
  exact value_independent_of_unreachable_fuel c h_valid.2 i h_i_input (total_nodes c) v h_no_reach

-- ============================================================================
-- Main Theorem: Unreachable Input Elimination
-- ============================================================================

/-- Main theorem: If input `i` does not reach any output, then the circuit's
    satisfaction is independent of the value assigned to `i`.

    Specifically, for any assignment, satisfying the circuit is equivalent
    to satisfying it with `i` fixed to `false`. -/
theorem unreachable_input_irrelevant
    (c : Circuit)
    (h_valid : circuit_valid c)
    (i : ℕ) (h_i_input : i < c.num_inputs)
    (h_unreach : ¬reaches_output c i) :
    ∀ assignment : ℕ → Bool,
      circuit_satisfied c assignment ↔
      circuit_satisfied c (Function.update assignment i false) := by
  intro assignment
  unfold circuit_satisfied
  constructor
  · -- Forward: if assignment satisfies, so does the updated one
    intro h_sat out h_out_mem
    -- Since i doesn't reach any output, it doesn't reach `out`
    have h_no_reach_out : ¬ReachesOrEq c i out := by
      intro h_reach
      apply h_unreach
      use out
      exact ⟨h_out_mem, h_reach⟩
    -- Apply the coincidence lemma
    have h_indep := value_independent_of_unreachable c h_valid i h_i_input out h_no_reach_out assignment
    -- Relate the original assignment to the updated one
    -- We need to show: eval_node c (update assignment i false) out = true
    -- We know: eval_node c assignment out = true (from h_sat)
    -- We know: eval_node c (update assignment i true) out = eval_node c (update assignment i false) out
    -- Case on assignment i
    by_cases h_ai : assignment i = true
    · -- assignment i = true, so assignment = update assignment i true
      have h_eq : assignment = Function.update assignment i true := by
        ext x
        by_cases h_xi : x = i
        · simp [h_xi, h_ai, Function.update]
        · simp [Function.update, h_xi]
      rw [h_eq] at h_sat
      rw [← h_indep]
      exact h_sat out h_out_mem
    · -- assignment i = false, so assignment = update assignment i false
      push_neg at h_ai
      have h_ai' : assignment i = false := Bool.eq_false_iff.mpr h_ai
      have h_eq : assignment = Function.update assignment i false := by
        ext x
        by_cases h_xi : x = i
        · simp [h_xi, h_ai', Function.update]
        · simp [Function.update, h_xi]
      rw [h_eq] at h_sat
      exact h_sat out h_out_mem
  · -- Backward: if updated assignment satisfies, show original also does
    intro h_sat out h_out_mem
    have h_no_reach_out : ¬ReachesOrEq c i out := by
      intro h_reach
      apply h_unreach
      use out
      exact ⟨h_out_mem, h_reach⟩
    have h_indep := value_independent_of_unreachable c h_valid i h_i_input out h_no_reach_out assignment
    by_cases h_ai : assignment i = true
    · have h_eq : assignment = Function.update assignment i true := by
        ext x
        by_cases h_xi : x = i
        · simp [h_xi, h_ai, Function.update]
        · simp [Function.update, h_xi]
      rw [h_eq, h_indep]
      exact h_sat out h_out_mem
    · push_neg at h_ai
      have h_ai' : assignment i = false := Bool.eq_false_iff.mpr h_ai
      have h_eq : assignment = Function.update assignment i false := by
        ext x
        by_cases h_xi : x = i
        · simp [h_xi, h_ai', Function.update]
        · simp [Function.update, h_xi]
      rw [h_eq]
      exact h_sat out h_out_mem

-- ============================================================================
-- Corollary: Satisfiability Preservation
-- ============================================================================

/-- Corollary: The existence of a satisfying assignment is preserved
    when fixing an unreachable input to false. -/
theorem unreachable_input_sat_equiv
    (c : Circuit)
    (h_valid : circuit_valid c)
    (i : ℕ) (h_i_input : i < c.num_inputs)
    (h_unreach : ¬reaches_output c i) :
    (∃ assignment, circuit_satisfied c assignment) ↔
    (∃ assignment, circuit_satisfied c (Function.update assignment i false)) := by
  constructor
  · intro ⟨assignment, h_sat⟩
    use assignment
    exact (unreachable_input_irrelevant c h_valid i h_i_input h_unreach assignment).mp h_sat
  · intro ⟨assignment, h_sat⟩
    use Function.update assignment i false

end CSP.L2S
