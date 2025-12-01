# CSP: A Formalization in Lean of Constraint Satisfaction Problems

This Lean 4 project formalizes Constraint Satisfaction Problems (CSPs), with proofs of equivalence, equisatisfiability, and symmetry-breaking. The **L2S (LeanToSolver)** framework enables using Lean as a constraint programming language with automatic export to MiniZinc and SMT-LIB.

## Project Structure

```
CSP/
├── Core.lean                 # General CSP definitions
├── Symmetry.lean             # General symmetry theory
├── Equivalence.lean          # General equivalence theory
├── GlobalConstraints.lean    # Predefined constraints
├── Transport.lean            # Type casting utilities
│
└── L2S/                      # LeanToSolver framework
    ├── Core.lean             # HomogeneousCSP foundations
    ├── Constraints.lean      # 50+ constraint types
    ├── Translate.lean        # Unified translation API
    ├── Backends/
    │   ├── MiniZinc.lean     # MiniZinc code generation
    │   └── SMTLIB.lean       # SMT-LIB code generation
    ├── Embedding.lean        # Embedding to heterogeneous CSP
    ├── Equivalence.lean      # Equivalence theory
    ├── Symmetry.lean         # Symmetry breaking theory
    ├── Proofs/               # Verified theorems (see below)
    └── Tests/                # 32 example problems
```

## Verified Proofs

### Symmetry Breaking

| File | Problem | Symmetry | Constraint |
|------|---------|----------|------------|
| `NQueensSB.lean` | N-Queens | Horizontal reflection | First queen in upper half |
| `GraphColoringSB.lean` | Graph Coloring | Color swap (0 ↔ c) | Node 0 has color 0 |
| `LatinSquareSB.lean` | Latin Square | Column permutation | First row sorted |

### Equivalence Proofs

| File | Formulations | Method |
|------|--------------|--------|
| `NQueensEquivalence.lean` | 1D (column vars) ↔ 2D (cell vars) | π-equivalence via projection |
| `GraphColoringEquivalence.lean` | Vertex model ↔ Binary matrix | π-equivalence via one-hot encoding |

### Circuit Optimization Theorems

| File | Result |
|------|--------|
| `UnreachableInputElimination.lean` | Inputs with no path to outputs can be fixed to any value |
| `ParityPathTheorem.lean` | Inputs with uniform parity to all outputs can be optimally fixed |

## Requirements

| Tool | Purpose | Link |
|------|---------|------|
| **Lean 4** | Theorem prover (required) | [lean-lang.org/install](https://lean-lang.org/install/) |
| **MiniZinc** | Constraint solver (optional) | [minizinc.org](https://www.minizinc.org/downloads/) |
| **Z3** | SMT solver (optional) | [github.com/Z3Prover/z3](https://github.com/Z3Prover/z3/releases) |
| **CVC5** | SMT solver (optional) | [github.com/cvc5/cvc5](https://github.com/cvc5/cvc5/releases) |

It is very recommended to have [elan](https://lean-lang.org/install/manual/) installed to avoid building Mathlib. You can install it this way:

```bash
# Install git and curl
sudo apt install git curl

# Install elan (choose 1 to accept the default install option)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Add the elan executables to the PATH
source $HOME/.elan/env
```

Once `elan` is installed, it will manage all Lean versions for you automatically.

## Building the Project

Even if you have installed Lean and `elan` with using the VS Code extension, you will need to build the project using the following commands to avoid building Mathlib from source:

```bash
# 1. Clone the repository
git clone https://github.com/leansolving/leancsp.git
cd leancsp

# 2. Download pre-built Mathlib cache (IMPORTANT: saves 30+ min build time)
lake exe cache get

# 3. Build the project
lake build
```

Once the project is built, you will be able to open it in your editor (VS Code recommended) and do not wait for Mathlib to build.

## Usage

### Modelling CSPs

The L2S framework uses `HomogeneousCSP` with a number of variables and a list of constraints:

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

def graph_coloring (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : HomogeneousCSP :=
  let bounds := (List.finRange nodes).map fun v => bound v 1 colors
  let edge_constrs := edges.map fun (u, v) => not_equal u v
  ⟨nodes, bounds ++ edge_constrs⟩
```

Available constraints: `alldifferent`, `count`, `element`, `sum_eq`, `linear_eq`, `less_than`, `not_equal`, `bound`, and 40+ more (see `L2S/Constraints.lean`).

### Solver Translation

Export CSPs to MiniZinc or SMT-LIB:

```lean
import CSP.L2S.Translate

open CSP.L2S

def my_csp : HomogeneousCSP := ...

-- Save to file
def main : IO Unit := do
  saveTo my_csp "model.mzn" BackendType.MiniZinc
  saveTo my_csp "model.smt2" BackendType.SMTLIB
```

Convenience functions:
```lean
translateTo my_csp BackendType.MiniZinc     -- Returns MiniZinc string
translateTo my_csp BackendType.SMTLIB       -- Returns SMT-LIB string
```

### Solving

After generating solver files:

```bash
# Run Lean to generate files
lake env lean --run CSP/L2S/Tests/lean/08_queens.lean

# Solve with MiniZinc
minizinc model.mzn

# Or solve with Z3
z3 model.smt2

# Or solve with CVC5
cvc5 model.smt2
```

## Example: Petersen Graph Coloring

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Translate

open CSP.L2S

def petersen : HomogeneousCSP :=
  let nodes := 10
  let edges := [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),  -- outer pentagon
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),  -- inner pentagram
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)   -- connections
  ]
  let bounds := (List.finRange nodes).map fun v => bound v 1 3
  let edge_constrs := edges.map fun (u, v) => not_equal ⟨u, by omega⟩ ⟨v, by omega⟩
  ⟨nodes, bounds ++ edge_constrs⟩

def main : IO Unit := do
  saveTo petersen "petersen.mzn" BackendType.MiniZinc
```

Run:
```bash
lake env lean --run MyFile.lean
minizinc petersen.mzn
```

## Main Definitions

### CSP Equivalence

Two CSPs are equivalent if there exists a bijection between their solution sets:

```lean
def equivalent (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) : Prop :=
  ∃ f : {x // x ∈ sol_set csp₁} → {x // x ∈ sol_set csp₂}, Function.Bijective f
```

### CSP Equisatisfiability

Two CSPs are equisatisfiable if satisfiability is preserved:

```lean
def equisatisfiable (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) : Prop :=
  is_satisfiable csp₁ ↔ is_satisfiable csp₂
```
