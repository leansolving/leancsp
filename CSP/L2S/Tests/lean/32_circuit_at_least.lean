import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed
import Mathlib.Tactic.Linarith

open CSP.L2S
open CSP.L2S.Tests.Timed
open CSP.L2S.IntCSP


/-!
# Circuit Satisfiability with at least k inputs

We assume that the number of outputs of the circuit is 1.

Problem: given a circuit, is it satisfiable whenever we set at least k inputs
to true?

CSP formulation:
  - Constraints encoding the circuit
  - Cardinality constraint
  - Negation of circuit satisfiability (what we want to prove)

If the CSP has a solution, it is a counter-example.
If the CSP is unsatisfiable, then for all inputs with at least 2 ones, the circuit
outputs true (what we want to prove).

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
def make_gate_constraints (num_nodes : ℕ) (gates : List Gate) : List (IntConstraint num_nodes) :=
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
-- Single Circuit to constraints
-- ============================================================================

/--
Convert a single circuit to a CSP.
All nodes have domain [0, 1] (Boolean values).
-/
def circuit_to_constraints (circuit : Circuit) (total_nodes : ℕ) : List (IntConstraint total_nodes) :=
  make_gate_constraints total_nodes circuit.gates


-- ============================================================================
-- CSP definition
-- ============================================================================

def at_least_k_satisfies_circuit_csp (circuit : Circuit) (k : ℕ) : IntCSP :=
  -- Compute the number of variables (must account for all gates' outputs)
  let total_nodes := circuit.gates.foldl (fun acc g => max acc g.output) circuit.num_inputs + 1

  -- Bounds for all nodes
  let bounds := (List.finRange total_nodes).map (fun i => bound i 0 1)

  -- Gate constraints
  let circuit_constrs := circuit_to_constraints circuit total_nodes

  -- At least k inputs constraint: sum(input_vars) ≥ k
  let circuit_inputs := List.range circuit.num_inputs
  let at_least_k_constr := match listToFinVector circuit_inputs total_nodes with
    | some ⟨_, input_vec⟩ => [at_least_k input_vec k]
    | none => []

  -- Negation of satisfiability constraint: output ≠ 1
  let output_node := circuit.gates.foldl (fun acc g => max acc g.output) 0
  let output_constr := if h : output_node < total_nodes then
    [not_equals_const ⟨output_node, h⟩ 1]
  else []

  ⟨total_nodes, bounds ++ circuit_constrs ++ at_least_k_constr ++ output_constr⟩


-- ============================================================================
-- Example: 3-input Majority Circuit (Full Adder Carry)
-- ============================================================================

/-!
3-input MAJORITY circuit (Full Adder CARRY output)

Inputs: A (node 0), B (node 1), C (node 2)
Output: CARRY (node 6)

Equation: CARRY = AB + BC + AC (output 1 iff at least 2 of 3 inputs are 1)

Gate structure:
- G1 = A AND B (node 3)
- G2 = B AND C (node 4)
- G3 = A AND C (node 5)
- CARRY = G1 OR G2 OR G3 (node 6)

Satisfiability properties:
- With k ≤ 1 input set to 1: UNSAT (cannot output 1)
- With k ≥ 2 inputs set to 1: SAT (can output 1)

This is the classic "2-of-3" threshold function.
-/
def majority3_circuit : Circuit := {
  num_inputs := 3,
  num_outputs := 1,
  gates := [
    ⟨[0, 1], GateType.AND, 3⟩,     -- G1 = A AND B
    ⟨[1, 2], GateType.AND, 4⟩,     -- G2 = B AND C
    ⟨[0, 2], GateType.AND, 5⟩,     -- G3 = A AND C
    ⟨[3, 4, 5], GateType.OR, 6⟩    -- CARRY = G1 OR G2 OR G3
  ]
}

-- ============================================================================
-- CSP translation to MiniZinc
-- ============================================================================

def main : IO Unit := do
  saveAllBackendsAutoTimed (at_least_k_satisfies_circuit_csp majority3_circuit 2)
