import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Translate
import CSP.L2S.Proofs.UnreachableInputElimination

/-!
# Parity Path Theorem - Circuit Benchmark Generator

Generates Boolean circuit benchmarks for testing the Parity Path Theorem in Lean.

## Features

- Generates circuits with uniform-parity inputs (all paths to outputs have same parity)
- Base version: circuit CSP without input fixing
- SBC version: circuit CSP with uniform-parity input fixed to optimal value

## Parity Rules

- **Even parity** (0 NOT gates mod 2): Input appears "positively" → fix to 1 (true)
- **Odd parity** (1 NOT gate mod 2): Input appears "negatively" → fix to 0 (false)

## Circuit Types

1. **Monotone AND-tree**: All inputs have parity 0, fix to 1
2. **Monotone OR-tree**: All inputs have parity 0, fix to 1
3. **Negated-input AND-tree**: Inputs pass through NOT, parity 1, fix to 0
4. **Negated-input OR-tree**: Inputs pass through NOT, parity 1, fix to 0
5. **Layered circuits**: Multiple levels with uniform parity preservation
6. **Majority circuits**: Majority function as AND/OR network
-/

namespace CSP.L2S.Proofs.Experiments

open CSP.L2S

-- ============================================================================
-- Circuit Data Structures (imported from UnreachableInputElimination)
-- ============================================================================

-- GateType, Gate, Circuit, total_nodes are already defined in CSP.L2S namespace

-- ============================================================================
-- Circuit-to-CSP Conversion (replicated from ParityPathCSP)
-- ============================================================================

/-- Generate a single gate constraint based on gate type.
    Returns None if indices are out of bounds. -/
def gateToConstraint (num_vars : ℕ) (g : Gate) : Option (TaggedConstraint num_vars) :=
  match g.gate_type with
  | GateType.AND =>
    match g.inputs with
    | [in1, in2] =>
      if h1 : in1 < num_vars then
        if h2 : in2 < num_vars then
          if h3 : g.output < num_vars then
            some (and_gate ⟨in1, h1⟩ ⟨in2, h2⟩ ⟨g.output, h3⟩)
          else none
        else none
      else none
    | _ => none
  | GateType.OR =>
    match g.inputs with
    | [in1, in2] =>
      if h1 : in1 < num_vars then
        if h2 : in2 < num_vars then
          if h3 : g.output < num_vars then
            some (or_gate ⟨in1, h1⟩ ⟨in2, h2⟩ ⟨g.output, h3⟩)
          else none
        else none
      else none
    | _ => none
  | GateType.NOT =>
    match g.inputs with
    | [in1] =>
      if h1 : in1 < num_vars then
        if h2 : g.output < num_vars then
          some (not_gate ⟨in1, h1⟩ ⟨g.output, h2⟩)
        else none
      else none
    | _ => none
  | GateType.XOR => none  -- Excluded from monotone circuits

/-- Convert all gates to constraints -/
def gatesToConstraints (num_vars : ℕ) (gates : List Gate) : List (TaggedConstraint num_vars) :=
  gates.filterMap (gateToConstraint num_vars)

/-- Convert a circuit to a IntCSP.
    Variables: indices 0 to total_nodes-1
    Constraints: bounds {0,1}, gate constraints, output=1 for each output node -/
def circuitCSP (c : Circuit) : IntCSP :=
  let n := total_nodes c
  -- Bound all variables to {0, 1}
  let bounds := (List.finRange n).map fun i => bound i 0 1
  -- Convert gates to constraints
  let gateConstrs := gatesToConstraints n c.gates
  -- Output must be 1 (true)
  let outputConstrs := c.output_nodes.filterMap fun out =>
    if h : out < n then some (equals_const ⟨out, h⟩ 1) else none
  ⟨n, bounds ++ gateConstrs ++ outputConstrs⟩

/-- Convert a circuit to a CSP with an input fixed to a specific Boolean value -/
def circuitCSPWithFixedInput (c : Circuit) (i : ℕ) (val : Bool) : IntCSP :=
  let base := circuitCSP c
  let fixVal : ℤ := if val then 1 else 0
  if h : i < base.num_vars then
    base.addConstraint (equals_const ⟨i, h⟩ fixVal)
  else
    base

/-- Helper to add multiple fixed-input constraints to a CSP -/
def addFixedInputConstraints (csp : IntCSP) (inputs : List ℕ) (val : Bool) : IntCSP :=
  let fixVal : ℤ := if val then 1 else 0
  inputs.foldl (fun acc i =>
    if h : i < acc.num_vars then
      acc.addConstraint (equals_const ⟨i, h⟩ fixVal)
    else acc) csp

/-- Convert a circuit to a CSP with half of the inputs fixed to the optimal value.
    Fixes inputs 0 to (numInputs/2 - 1). -/
def circuitCSPWithHalfFixedInputs (c : Circuit) (val : Bool) : IntCSP :=
  let base := circuitCSP c
  let halfInputs := c.num_inputs / 2
  let inputsToFix := List.range halfInputs
  addFixedInputConstraints base inputsToFix val

-- ============================================================================
-- Circuit Generators
-- ============================================================================

/-- Helper: Build a binary tree of gates from a list of nodes.
    Uses fuel to ensure termination. -/
def buildBinaryTree (gateType : GateType) (nodes : List ℕ) (nextNode : ℕ) (fuel : ℕ) :
    List Gate × ℕ :=
  match fuel with
  | 0 => ([], nodes.head?.getD nextNode)
  | fuel' + 1 =>
    match nodes with
    | [] => ([], nextNode)
    | [single] => ([], single)
    | _ =>
      -- Pair up nodes and create gates
      let rec pairUp (remaining : List ℕ) (nodeIdx : ℕ) (acc : List Gate) (nextLevel : List ℕ) :
          List Gate × List ℕ × ℕ :=
        match remaining with
        | [] => (acc, nextLevel, nodeIdx)
        | [a] => (acc, nextLevel ++ [a], nodeIdx)  -- Odd node carries over
        | a :: b :: rest =>
          let gate : Gate := ⟨[a, b], gateType, nodeIdx⟩
          pairUp rest (nodeIdx + 1) (acc ++ [gate]) (nextLevel ++ [nodeIdx])
      let (gates, nextLevel, nextIdx) := pairUp nodes nextNode [] []
      let (moreGates, finalOutput) := buildBinaryTree gateType nextLevel nextIdx fuel'
      (gates ++ moreGates, finalOutput)

/-- Generate a monotone AND-tree circuit.
    All inputs have parity 0 → fix to 1. -/
def generateAndTree (numInputs : ℕ) : Circuit :=
  let inputs := List.range numInputs
  let fuel := numInputs  -- Enough fuel for log2(n) iterations
  let (gates, finalOutput) := buildBinaryTree GateType.AND inputs numInputs fuel
  { num_inputs := numInputs
    num_outputs := 1
    gates := gates
    output_nodes := [finalOutput] }

/-- Generate a monotone OR-tree circuit.
    All inputs have parity 0 → fix to 1. -/
def generateOrTree (numInputs : ℕ) : Circuit :=
  let inputs := List.range numInputs
  let fuel := numInputs
  let (gates, finalOutput) := buildBinaryTree GateType.OR inputs numInputs fuel
  { num_inputs := numInputs
    num_outputs := 1
    gates := gates
    output_nodes := [finalOutput] }

/-- Generate an AND-tree where all inputs first pass through NOT gates.
    All inputs have parity 1 → fix to 0. -/
def generateNegatedAndTree (numInputs : ℕ) : Circuit :=
  -- First, create NOT gates for all inputs
  let notGates := List.range numInputs |>.map fun i =>
    (⟨[i], GateType.NOT, numInputs + i⟩ : Gate)
  let negatedInputs := List.range numInputs |>.map fun i => numInputs + i
  -- Then build AND tree on negated inputs
  let fuel := numInputs
  let (treeGates, finalOutput) := buildBinaryTree GateType.AND negatedInputs (2 * numInputs) fuel
  let allGates := notGates ++ treeGates
  { num_inputs := numInputs
    num_outputs := 1
    gates := allGates
    output_nodes := [finalOutput] }

/-- Generate an OR-tree where all inputs first pass through NOT gates.
    All inputs have parity 1 → fix to 0. -/
def generateNegatedOrTree (numInputs : ℕ) : Circuit :=
  let notGates := List.range numInputs |>.map fun i =>
    (⟨[i], GateType.NOT, numInputs + i⟩ : Gate)
  let negatedInputs := List.range numInputs |>.map fun i => numInputs + i
  let fuel := numInputs
  let (treeGates, finalOutput) := buildBinaryTree GateType.OR negatedInputs (2 * numInputs) fuel
  let allGates := notGates ++ treeGates
  { num_inputs := numInputs
    num_outputs := 1
    gates := allGates
    output_nodes := [finalOutput] }

/-- Helper: Build layered circuit with alternating gate types -/
def buildLayeredCircuit (nodes : List ℕ) (nextNode : ℕ) (layerIdx numLayers : ℕ) (fuel : ℕ) :
    List Gate × ℕ :=
  match fuel with
  | 0 => ([], nodes.head?.getD nextNode)
  | fuel' + 1 =>
    if layerIdx ≥ numLayers ∨ nodes.length ≤ 1 then
      ([], nodes.head?.getD (nextNode - 1))
    else
      let gateType := if layerIdx % 2 == 0 then GateType.AND else GateType.OR
      let rec pairUp (remaining : List ℕ) (nodeIdx : ℕ) (acc : List Gate) (nextLevel : List ℕ) :
          List Gate × List ℕ × ℕ :=
        match remaining with
        | [] => (acc, nextLevel, nodeIdx)
        | [a] => (acc, nextLevel ++ [a], nodeIdx)
        | a :: b :: rest =>
          let gate : Gate := ⟨[a, b], gateType, nodeIdx⟩
          pairUp rest (nodeIdx + 1) (acc ++ [gate]) (nextLevel ++ [nodeIdx])
      let (gates, nextLevel, nextIdx) := pairUp nodes nextNode [] []
      let (moreGates, finalOutput) := buildLayeredCircuit nextLevel nextIdx (layerIdx + 1) numLayers fuel'
      (gates ++ moreGates, finalOutput)

/-- Generate a layered circuit with alternating AND/OR layers.
    All inputs have uniform parity 0 → fix to 1. -/
def generateLayeredCircuit (numInputs numLayers : ℕ) : Circuit :=
  let inputs := List.range numInputs
  let fuel := numInputs + numLayers
  let (gates, finalOutput) := buildLayeredCircuit inputs numInputs 0 numLayers fuel
  { num_inputs := numInputs
    num_outputs := 1
    gates := gates
    output_nodes := [finalOutput] }

/-- Helper to build a chain of AND gates -/
def buildAndChain (inputs : List ℕ) (startNode : ℕ) : List Gate × ℕ :=
  match inputs with
  | [] => ([], startNode)
  | [single] => ([], single)
  | first :: rest =>
    let (gates, _, finalNode) := rest.foldl
      (fun (acc, prevNode, nextIdx) inp =>
        let gate : Gate := ⟨[prevNode, inp], GateType.AND, nextIdx⟩
        (acc ++ [gate], nextIdx, nextIdx + 1))
      ([], first, startNode)
    (gates, finalNode - 1)

/-- Generate a majority circuit.
    Output is 1 iff more than n/2 inputs are 1.
    All inputs have uniform parity 0 → fix to 1. -/
def generateMajorityCircuit (numInputs : ℕ) : Circuit :=
  if numInputs ≤ 2 then
    if numInputs == 2 then
      { num_inputs := 2
        num_outputs := 1
        gates := [⟨[0, 1], GateType.AND, 2⟩]
        output_nodes := [2] }
    else
      { num_inputs := numInputs
        num_outputs := 1
        gates := []
        output_nodes := [0] }
  else if numInputs == 3 then
    -- Majority of 3: (a AND b) OR (a AND c) OR (b AND c)
    let ab : Gate := ⟨[0, 1], GateType.AND, 3⟩
    let ac : Gate := ⟨[0, 2], GateType.AND, 4⟩
    let bc : Gate := ⟨[1, 2], GateType.AND, 5⟩
    let abOrAc : Gate := ⟨[3, 4], GateType.OR, 6⟩
    let result : Gate := ⟨[6, 5], GateType.OR, 7⟩
    { num_inputs := 3
      num_outputs := 1
      gates := [ab, ac, bc, abOrAc, result]
      output_nodes := [7] }
  else
    -- For larger inputs: AND of first half OR AND of second half
    let mid := numInputs / 2
    let firstHalf := List.range mid
    let secondHalf := List.range (numInputs - mid) |>.map (· + mid)
    -- Build AND chain for first half
    let (firstGates, firstResult) := buildAndChain firstHalf numInputs
    let nextNode := if firstGates.isEmpty then numInputs else
      firstGates.foldl (fun acc g => max acc g.output) numInputs + 1
    -- Build AND chain for second half
    let (secondGates, secondResult) := buildAndChain secondHalf nextNode
    let nextNode' := if secondGates.isEmpty then nextNode else
      secondGates.foldl (fun acc g => max acc g.output) nextNode + 1
    -- OR the two results
    let orGate : Gate := ⟨[firstResult, secondResult], GateType.OR, nextNode'⟩
    { num_inputs := numInputs
      num_outputs := 1
      gates := firstGates ++ secondGates ++ [orGate]
      output_nodes := [nextNode'] }

-- ============================================================================
-- CSP Generation
-- ============================================================================

/-- Save a circuit as base, SBC (1 fixed), and SBC-half (half fixed) CSP versions to all backends.
    - base: circuit without any input fixing
    - sbc: circuit with first input fixed to optimal value based on parity
    - sbc_half: circuit with half of inputs (0 to numInputs/2-1) fixed to optimal value -/
def saveCircuitPair (baseDir circuitType : String) (size : ℕ) (c : Circuit)
    (oddParity : Bool) : IO Unit := do
  -- Optimal value: even parity (false) → fix to 1 (true), odd parity (true) → fix to 0 (false)
  let optimalValue := !oddParity

  let baseCSP := circuitCSP c
  let sbcCSP := circuitCSPWithFixedInput c 0 optimalValue
  let sbcHalfCSP := circuitCSPWithHalfFixedInputs c optimalValue

  let halfFixed := c.num_inputs / 2

  -- Save to both MiniZinc and SMT-LIB
  for backend in allBackends do
    let dirName := getBackendDirName backend
    let ext := getBackendExtension backend

    let outDir := s!"{baseDir}/{dirName}/{circuitType}"
    let fp := System.FilePath.mk outDir
    IO.FS.createDirAll fp

    let baseContent := translateTo baseCSP backend
    let sbcContent := translateTo sbcCSP backend
    let sbcHalfContent := translateTo sbcHalfCSP backend

    IO.FS.writeFile s!"{outDir}/base_{size}.{ext}" baseContent
    IO.FS.writeFile s!"{outDir}/sbc_{size}.{ext}" sbcContent
    IO.FS.writeFile s!"{outDir}/sbc_half_{size}.{ext}" sbcHalfContent

  IO.println s!"  {circuitType}_{size}: {total_nodes c} vars, {c.gates.length} gates, {halfFixed} inputs fixed in sbc_half"

-- ============================================================================
-- Batch Generation
-- ============================================================================

/-- Generate all circuit benchmarks. -/
def generateCircuitBenchmarks (outputDir : String) : IO Unit := do
  IO.println "Generating Parity Path Theorem Circuit Benchmarks"
  IO.println s!"Output directory: {outputDir}"
  IO.println ""

  -- AND trees: larger sizes for overhead-dominated comparison
  IO.println "=== AND Trees (parity 0 → fix to 1) ==="
  for size in [8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096] do
    let circuit := generateAndTree size
    saveCircuitPair outputDir "and_tree" size circuit false

  IO.println ""

  -- OR trees: larger sizes
  IO.println "=== OR Trees (parity 0 → fix to 1) ==="
  for size in [8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096] do
    let circuit := generateOrTree size
    saveCircuitPair outputDir "or_tree" size circuit false

  IO.println ""

  -- Negated AND trees: larger sizes
  IO.println "=== Negated AND Trees (parity 1 → fix to 0) ==="
  for size in [8, 16, 32, 64, 128, 256, 512, 1024, 2048] do
    let circuit := generateNegatedAndTree size
    saveCircuitPair outputDir "neg_and_tree" size circuit true

  IO.println ""

  -- Negated OR trees: larger sizes
  IO.println "=== Negated OR Trees (parity 1 → fix to 0) ==="
  for size in [8, 16, 32, 64, 128, 256, 512, 1024, 2048] do
    let circuit := generateNegatedOrTree size
    saveCircuitPair outputDir "neg_or_tree" size circuit true

  IO.println ""

  -- Layered circuits: larger sizes for harder problems
  IO.println "=== Layered Circuits (parity 0 → fix to 1) ==="
  for size in [8, 16, 32, 64, 128, 256, 512, 1024, 2048] do
    let circuit := generateLayeredCircuit size 4  -- 4 layers for more complexity
    saveCircuitPair outputDir "layered" size circuit false

  IO.println ""

  -- Majority circuits: larger sizes
  IO.println "=== Majority Circuits (parity 0 → fix to 1) ==="
  for size in [3, 5, 7, 9, 11, 15, 21, 31, 51, 71] do
    let circuit := generateMajorityCircuit size
    saveCircuitPair outputDir "majority" size circuit false

  IO.println ""
  IO.println "=== Generation complete ==="

-- ============================================================================
-- Main Entry Point
-- ============================================================================

/-- Main function: generate all benchmarks to the default output directory. -/
def main : IO Unit := do
  let outputDir := "CSP/L2S/Proofs"
  generateCircuitBenchmarks outputDir

end CSP.L2S.Proofs.Experiments
