# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build Commands

```bash
# Download pre-built Mathlib cache (critical - saves 30+ minutes)
lake exe cache get

# Build the project
lake build

# Run a test file (generates .mzn/.smt2 output)
lake env lean --run CSP/L2S/Tests/lean/08_queens.lean

# Solve generated files
minizinc model.mzn
z3 model.smt2
cvc5 model.smt2
```

## Architecture

This is a Lean 4 formalization of Constraint Satisfaction Problems with the **L2S (LeanToSolver)** framework for exporting to MiniZinc and SMT-LIB.

### Two-Layer CSP Structure

1. **Heterogeneous CSP** (`CSP/Core.lean`): General CSP with type-safe heterogeneous domains. Variables can have different domain types via dependent types (`DomainType : VarIndex → Type`).

2. **Homogeneous CSP** (`CSP/L2S/Core.lean`): Specialized for solver translation. All variables use integer domain (`ℤ`). Uses dual representation:
   - `ConstraintPattern`: Semantic structure for MiniZinc/SMT-LIB translation
   - `DynamicConstraint`: Executable checker for Lean proofs

### L2S Translation Pipeline

```
HomogeneousCSP → Backend.translateWith → MiniZinc/SMTLIB string
```

Key files:
- `CSP/L2S/Constraints.lean`: 50+ constraint constructors (alldifferent, sum, count, boolean gates, etc.)
- `CSP/L2S/Backend.lean`: Backend interface definition
- `CSP/L2S/Backends/MiniZinc.lean`: MiniZinc code generation
- `CSP/L2S/Backends/SMTLIB.lean`: SMT-LIB code generation
- `CSP/L2S/Translate.lean`: Unified API (`translateTo`, `saveTo`)

### Adding New Constraints

1. Add pattern variant to `ConstraintPattern` in `CSP/L2S/Core.lean`
2. Create constructor function in `CSP/L2S/Constraints.lean`
3. Add translation case in both `Backends/MiniZinc.lean` and `Backends/SMTLIB.lean`

### Proof Modules

Located in `CSP/L2S/Proofs/`:
- Symmetry breaking proofs (N-Queens, Graph Coloring, Latin Square)
- Equivalence proofs between CSP formulations
- Circuit optimization theorems

## Git Commit Rules

- Never mention Claude Code in commit messages
- Keep commit messages brief
- For commits to main branch: show the planned message to the user before committing

## Dependencies

- Lean 4 v4.24.0-rc1
- Mathlib (via lake cache)
- Canonical (chasenorman/Canonical)
