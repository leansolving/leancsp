import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed
open CSP.L2S.IntCSP

/-!
# Circuit Equivalence Checking with Proper Circuit Structure

This example demonstrates equivalence checking using a proper Circuit data structure,
following the same pattern as graph coloring where the graph (nodes, edges) is a
separate structure passed as a parameter.

## Approach
1. Define Circuit structure (inputs, outputs, gates)
2. Define two separate circuits
3. Create equivalence CSP from the two circuit structures
4. Verify: UNSATISFIABLE = equivalent, SATISFIABLE = different (with counterexample)
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


-- ============================================================================
-- Constraint Generation from Circuit
-- ============================================================================

/-- Generate CSP constraints for a list of gates -/
def make_gate_constraints (num_nodes : ℕ) (gates : List Gate) : List (TaggedConstraint num_nodes) :=
  gates.filterMap fun g =>
    match g.gate_type with
    | GateType.AND =>
        -- Handle arbitrary-arity AND gates
        if h_output : g.output < num_nodes then
          match listToFinVector g.inputs num_nodes with
          | some ⟨_, input_vec⟩ => some (and_all input_vec ⟨g.output, h_output⟩)
          | none => none
        else none

    | GateType.OR =>
        -- Handle arbitrary-arity OR gates
        if h_output : g.output < num_nodes then
          match listToFinVector g.inputs num_nodes with
          | some ⟨_, input_vec⟩ => some (or_all input_vec ⟨g.output, h_output⟩)
          | none => none
        else none

    | GateType.XOR =>
        -- Handle arbitrary-arity XOR gates (parity)
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
                -- NOT gate: out = ¬in
                some (not_gate ⟨in1, h1⟩ ⟨g.output, h2⟩)
              else none
            else none
        | _ => none

-- ============================================================================
-- Single Circuit to CSP
-- ============================================================================

/--
Convert a single circuit to a CSP.
All nodes have domain [0, 1] (Boolean values).
-/
def circuit_to_constraints (circuit : Circuit) (total_nodes : ℕ) : List (TaggedConstraint total_nodes) :=
  make_gate_constraints total_nodes circuit.gates

-- ============================================================================
-- Equivalence Checking: Compare Two Circuits
-- ============================================================================

/--
Create an equivalence checking CSP for two circuits.

The two circuits MUST have:
- Same number of inputs (shared)
- Same number of outputs (to be compared)

Node allocation:
- Nodes 0..n-1: Shared inputs
- Circuit 1 uses nodes starting from n
- Circuit 2 uses nodes starting from (n + circuit1_internal_nodes)

Returns CSP with negated equivalence constraints: output1_i ≠ output2_i for each output.
-/
def circuits_equivalence_csp (circuit1 circuit2 : Circuit)
    (circuit1_outputs circuit2_outputs : List ℕ) : IntCSP :=

  -- Calculate total nodes needed. We assume that both circuits share the same inputs
  let num_shared_inputs := circuit1.num_inputs
  let max_node1 := circuit1.gates.foldl (fun acc g => max acc g.output) num_shared_inputs
  let max_node2 := circuit2.gates.foldl (fun acc g => max acc g.output) num_shared_inputs
  let total_nodes := max max_node1 max_node2 + 1

  -- Bounds for all nodes
  let bounds := (List.finRange total_nodes).map (fun i => bound i 0 1)

  -- Gate constraints from both circuits
  let circuit1_constrs := circuit_to_constraints circuit1 total_nodes
  let circuit2_constrs := circuit_to_constraints circuit2 total_nodes

  -- Negated equivalence constraints: output1_i ≠ output2_i
  let equiv_constrs := circuit1_outputs.zip circuit2_outputs |>.filterMap fun (o1, o2) =>
    if h1 : o1 < total_nodes then
      if h2 : o2 < total_nodes then
        some (not_equal ⟨o1, h1⟩ ⟨o2, h2⟩)
      else none
    else none

  ⟨total_nodes, bounds ++ circuit1_constrs ++ circuit2_constrs ++ equiv_constrs⟩

-- ============================================================================
-- Example: XOR Equivalence
-- ============================================================================

/-
Circuit 1: Direct XOR
- Inputs: nodes 0 (a), 1 (b)
- Output: node 2 (out1 = a XOR b)
-/
def xor_direct : Circuit := {
  num_inputs := 2,
  num_outputs := 1,
  gates := [
    ⟨[0, 1], GateType.XOR, 2⟩  -- out1 = a XOR b
  ]
}

/-
Circuit 2: Decomposed XOR
- Inputs: nodes 0 (a), 1 (b) [SHARED with circuit 1]
- Internal: nodes 3 (not_a), 4 (not_b), 5 (a AND not_b), 6 (not_a AND b)
- Output: node 7 (out2 = (a AND not_b) OR (not_a AND b))
-/
def xor_decomposed : Circuit := {
  num_inputs := 2,
  num_outputs := 1,
  gates := [
    ⟨[0], GateType.NOT, 3⟩,        -- not_a
    ⟨[1], GateType.NOT, 4⟩,        -- not_b
    ⟨[0, 4], GateType.AND, 5⟩,     -- a AND not_b
    ⟨[3, 1], GateType.AND, 6⟩,     -- not_a AND b
    ⟨[5, 6], GateType.OR, 7⟩       -- out2
  ]
}

/--
Equivalence CSP for two XOR implementations.
Expected: UNSATISFIABLE (circuits are equivalent)
-/
def xor_equivalence : IntCSP :=
  circuits_equivalence_csp xor_direct xor_decomposed [2] [7]

-- ============================================================================
-- Main: Generate MiniZinc for Equivalence Check
-- ============================================================================

/-- Generate MiniZinc and SMT-LIB code for XOR equivalence checking -/
def main : IO Unit := do
  saveAllBackendsAutoTimed xor_equivalence
