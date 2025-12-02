# Proofs

Formal Lean 4 proofs for CSP symmetry breaking, equivalence, and circuit optimization theorems.

## Proof Files

### Symmetry Breaking (SB)

| File | Problem | Symmetry | Constraint |
|------|---------|----------|------------|
| `NQueensSB.lean` | N-Queens | Horizontal reflection | First queen in upper half |
| `GraphColoringSB.lean` | Graph Coloring | Color swap (0 ↔ c) | Node 0 has color 0 |
| `LatinSquareSB.lean` | Latin Square | Column permutation | First row sorted |

### Equivalence Proofs

| File | Formulations | Method |
|------|--------------|--------|
| `NQueensEquivalence.lean` | 1D (column vars) ↔ 2D (cell vars) | π-equivalence via projection/lifting |
| `GraphColoringEquivalence.lean` | Vertex model ↔ Binary matrix | π-equivalence via one-hot encoding |

### Circuit Theorems

| File | Result |
|------|--------|
| `UnreachableInputElimination.lean` | Inputs with no path to outputs can be fixed to any value |
| `ParityPathTheorem.lean` | Inputs with uniform parity to all outputs can be optimally fixed |

## Instance Generation

Running these Lean files generates `.mzn` and `.smt2` problem instances in `mzn/` and `smt2/` subdirectories. These instances are used by the experiment scripts.

## Experiments

The `Experiments/` subfolder contains Python scripts for benchmarking:
- Symmetry breaking effectiveness
- Parity Path Theorem circuit benchmarks
- π-equivalence verification via solution counting

See `Experiments/README.md` for details.
