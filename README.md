# LeanCSP

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4.30.0-blue.svg)](lean-toolchain)

A Lean 4 project formalizing Constraint Satisfaction Problems, with proofs of equivalence,
equisatisfiability, and symmetry breaking. The **L2S (LeanToSolver)** framework lets you use
Lean as a constraint programming language and export models to MiniZinc and SMT-LIB.

LeanCSP can also prove a CSP unsatisfiable. It compiles the model to pseudo-Boolean
constraints through a verified order encoding, runs an external PB solver, and re-checks the
solver's proof in Lean. The resulting theorems require no trust in the external solver.

## Requirements

| Tool | Purpose | Link |
|------|---------|------|
| **Lean 4** | Theorem prover (required) | [lean-lang.org/install](https://lean-lang.org/install/) |
| **MiniZinc** | Constraint solver (optional) | [minizinc.org](https://www.minizinc.org/downloads/) |
| **Z3 / cvc5** | SMT solvers (optional) | [z3](https://github.com/Z3Prover/z3/releases) / [cvc5](https://github.com/cvc5/cvc5/releases) |
| **RoundingSat** | PB solver, to generate a new certificate (optional) | [gitlab.com/MIAOresearch/software/roundingsat](https://gitlab.com/MIAOresearch/software/roundingsat) |
| **veripb** | PB proof elaborator, to generate a new certificate (optional) | [gitlab.com/MIAOresearch/software/VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) |

Make sure to have [elan](https://lean-lang.org/install/manual/) installed to avoid building
the Mathlib dependencies. Elan auto-downloads the correct Lean version:

```bash
# Install git and curl
sudo apt install git curl

# Install elan (choose 1 to accept the default install option)
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

# Add the elan executables to the PATH
source $HOME/.elan/env
```

RoundingSat and veripb are only needed to generate a new certificate. Re-checking the
committed ones needs nothing but Lean. The Lean dependency PBLean, which provides the
verified proof checker, is fetched automatically by Lake.

## Building the Project

```bash
# 1. Clone the repository
git clone https://github.com/leansolving/leancsp.git
cd leancsp

# 2. Download pre-built Mathlib cache (IMPORTANT: saves 30+ min build time)
lake exe cache get

# 3. Build the project
lake build
```

The lakefile builds every submodule, so a bare `lake build` also re-checks every committed
certificate. It ends with `Build completed successfully`.

## Usage

### Modelling CSPs

The L2S framework uses `IntCSP` with a number of variables and a list of constraints. A
variable's range comes from a `bound` constraint:

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

def graph_coloring (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : IntCSP :=
  let bounds := (List.finRange nodes).map fun v => bound v 1 colors
  let edge_constrs := edges.map fun (u, v) => not_equal u v
  ⟨nodes, bounds ++ edge_constrs⟩
```

Available constraints: `alldifferent`, `count`, `element`, `sum_eq`, `linear_eq`,
`not_equal`, `at_most_k`, `at_least_k`, `bound`, and 40+ more (see `L2S/Constraints.lean`).

### Solver translation

Export CSPs to MiniZinc or SMT-LIB:

```lean
import CSP.L2S.Translate

open CSP.L2S

def my_csp : IntCSP := ...

def main : IO Unit := do
  saveTo my_csp "model.mzn" BackendType.MiniZinc
  saveTo my_csp "model.smt2" BackendType.SMTLIB
```

Then solve the generated files:

```bash
lake env lean --run MyFile.lean

minizinc model.mzn
z3 model.smt2
cvc5 --produce-models model.smt2
```

### Proving unsatisfiability

Each instance is one line plus a committed certificate:

```lean
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiableInt :=
  csp_unsat_file php_3_2 3 "certs/php_3_2.pbp"
```

Everything else is derived from the CSP. To add your own instance, generate a certificate
with `experiments/gen_cert.py <Module> <cspExpr> <out>`, which needs `roundingsat` and
`veripb`, and prints the `numVars` argument to pass.

## How it works

1. **Encode.** `encodeCSP` compiles each constraint to pseudo-Boolean constraints over
   threshold variables, where an integer variable with domain `D` becomes bits "`x ≤ dⱼ`".
   One soundness theorem covers this step for every CSP, so instances need no proofs of
   their own.
2. **Solve.** The constraints are written as OPB, RoundingSat solves them, and veripb
   elaborates its log into a certificate committed under `Problems/certs/`.
3. **Check.** PBLean's verified checker re-runs the certificate against the Lean-side
   constraints, and `csp_unsat` turns the result into `¬ csp.isSatisfiableInt`. A bad
   certificate makes the check fail, so the theorem does not go through.

The same pattern works for satisfiability: `csp_sat_file` re-checks an external solver's
witness with kernel `decide`.

## Project structure

```
CSP/
├── Core.lean                 # General CSP definitions
├── Symmetry.lean             # General symmetry theory
├── Equivalence.lean          # General equivalence theory
├── GlobalConstraints.lean    # Predefined constraints
│
└── L2S/                      # LeanToSolver framework
    ├── Core.lean             # IntCSP foundations
    ├── Constraints.lean      # 50+ constraint types
    ├── Translate.lean        # Unified translation API
    ├── Symmetry.lean         # Symmetry breaking theory
    ├── Equivalence.lean      # Equivalence theory
    ├── ValuePrecedence.lean  # Value precedence as a symmetry break
    ├── Witness.lean          # SAT witness checking
    ├── Backends/
    │   ├── MiniZinc.lean     # MiniZinc code generation
    │   ├── SMTLIB.lean       # SMT-LIB code generation
    │   └── PB/               # Verified pseudo-Boolean UNSAT backend
    │       └── Problems/     # Instances and their certificates
    ├── Proofs/               # Verified theorems (see below)
    ├── EndToEnd/             # Results about the original CSPs
    └── Tests/                # 36 example problems

experiments/                  # Reproducible studies (see experiments/README.md)
```

## Verified Results

### UNSAT theorems

Instances live in `CSP/L2S/Backends/PB/Problems/`, each with a committed certificate. The
`*SBC.lean` and `*VP.lean` modules repeat these families with a symmetry-breaking constraint
added.

| Module | Certifies |
|--------|-----------|
| `Pigeonhole.lean` | `p` pigeons do not fit injectively into `h < p` holes |
| `GraphColoring.lean` | K₃ is not 2-colourable, K₄ is not 3-colourable |
| `OddCycle.lean` | C₅, C₇ and C₉ are not 2-colourable |
| `Schur.lean`, `Schur3.lean` | `{1..5}` has no sum-free 2-colouring, `{1..14}` none with 3 |
| `VanDerWaerden.lean` | Every 2-colouring of `{1..9}` has a monochromatic 3-term AP |
| `Ramsey.lean` | Every 2-colouring of K₆'s edges has a monochromatic triangle |
| `Paley.lean` | Paley(13) has no independent set of size 4 |
| `Langford.lean` | The Langford pairing L(2,2) has no solution |
| `Sudoku.lean`, `Latin.lean` | Instances with contradictory givens are unsolvable |
| `MagicHexagon.lean` | There is no order-2 normal magic hexagon |
| `MutilatedChessboard*.lean` | A 4×4 or 6×6 board minus two same-colour corners has no domino tiling |
| `NQueens.lean`, `BlockedQueens.lean` | 2- and 3-Queens, and 4-Queens with a blocked column, have no solution |
| `PeaceableArmies.lean` | No 3+3 peaceable queens fit on a 4×4 board |
| `Circuit.lean`, `CircuitEquiv.lean`, `FullAdder.lean`, `RippleCarry.lean` | Gate-level circuits meet their specifications |

`CSP/L2S/EndToEnd/` combines these with a verified symmetry break to state results about the
original CSP. `SchurCertify.lean` pairs a solver witness with a certificate to pin the exact
Schur numbers S(2) = 4 and S(3) = 13, and proves S(4) ≥ 44.

### Symmetry breaking

Each file proves a candidate constraint is a valid symmetry break, so adding it preserves
satisfiability.

| File | Problem | Symmetry | Constraint |
|------|---------|----------|------------|
| `NQueensSB.lean` | N-Queens | Horizontal reflection | First queen in the first half |
| `GraphColoringSB.lean` | Graph Coloring | Colour swap | Node 0 has colour 0 |
| `LatinSquareSB.lean` | Latin Square | Column permutation | First row sorted |
| `SudokuSB.lean` | Sudoku | Value swap | Cell (0,0) fixed |
| `SchurSB.lean` | Schur | Colour swap | `x₀ = 0` |
| `MatchingSB.lean` | Perfect matching | Vertex transposition | Order the swapped edge variables |
| `MutilatedSB.lean` | Mutilated chessboard | Diagonal reflection | Order the swapped domino variables |
| `LangfordSB.lean` | Langford | Sequence reversal | Digit 0 in the second half |

`ValuePrecedence.lean` proves the Law-Lee value precedence constraint sound for any CSP whose
solutions are closed under colour permutations; `*ValuePrecedence.lean` files discharge that
for graph colouring, Schur, Ramsey, van der Waerden and pigeonhole.

`SchurReversalCounterexample.lean` is the cautionary case: the strict lexicographic reversal
leader is sound for van der Waerden but not for ordinary Schur.

### Equivalence proofs

All use π-equivalence, an explicit projection and lifting between two formulations, which
transports both solutions and unsatisfiability across the reformulation.

| File | Formulations |
|------|--------------|
| `NQueensEquivalence.lean` | Column model ↔ board model |
| `GraphColoringEquivalence.lean` | Vertex model ↔ binary one-hot matrix |
| `LatinSquareEquivalence.lean` | Value-compact ↔ one-hot binary |
| `SudokuEquivalence.lean` | Value-compact ↔ one-hot expanded |
| `SchurEquivalence.lean` | Compact colour model ↔ binary matrix |
| `MutilatedEquivalence.lean` | Orientation model ↔ edge model |

### Circuit theorems

| File | Result |
|------|--------|
| `UnreachableInputElimination.lean` | Inputs with no path to outputs can be fixed to any value |
| `ParityPathTheorem.lean` | Inputs with uniform parity to all outputs can be optimally fixed |
| `CircuitInputSymmetryBreaking.lean` | Inputs with identical fanout can be ordered |

## Citing

If you use LeanCSP in your research, please cite the accompanying paper:

> Pablo Manrique and Stefan Szeider. *LeanCSP: A Framework for Certifying Constraint
> Reformulation and Solving in Lean.* arXiv preprint, 2026.

(A BibTeX entry with the arXiv identifier will be added once the preprint is announced.)

## License

Apache 2.0, see [LICENSE](LICENSE).
