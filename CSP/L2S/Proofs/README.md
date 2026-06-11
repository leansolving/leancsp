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
| `CircuitInputSymmetryBreaking.lean` | Lexicographic ordering on fully-symmetric inputs is a valid SBC |
| `CircuitTwinSymmetryBreaking.lean` | ⚠️ **Depends on 2 axioms** — Ordering any subset of twin (identical-fanout) inputs is a valid SBC |
| `UnreachableInputElimination.lean` | Inputs with no path to outputs can be fixed to any value |
| `ParityPathTheorem.lean` | Inputs with uniform parity to all outputs can be optimally fixed |

> ## ⚠️ Axiom status
>
> **Every proof here is axiom-clean (`propext, Classical.choice, Quot.sound`)
> except `CircuitTwinSymmetryBreaking.lean`.** That one file depends on two
> unproven `axiom`s inherited from the original development —
> `gate_constraint_preserved_by_twin_perm` and `ordering_constraint_satisfied_by_sort`
> — so its theorems are effectively **conjectures**. Check any theorem with
> `#print axioms <name>`. **New axioms must not be introduced; the two existing
> ones should be discharged into real proofs before this module is relied upon.**

### Shared Infrastructure

`PatternBridges.lean` provides the two-way `*_holds_iff` bridges from
`IntCSP.satisfiesConstraintInt` (= `patternHolds`) to the direct `Fin`-indexed
forms these proofs reason with (`bound_holds_iff`, `alldifferent_holds_iff`,
`sum_eq_holds_iff`, the N-Queens diagonal lemmas, …). The forward-only `*_sat`
bridges in `Backends/PB/` serve the UNSAT pipeline; symmetry proofs need both
directions because they transport solutions across permutations.

## Instance Generation

Each problem file defines `IO` helpers that emit `.mzn` and `.smt2` problem
instances into `mzn/` and `smt2/` subdirectories (created on demand via
`Translate.saveToAuto`), for external benchmarking of the verified
reformulations. The cert-era Python benchmarking harness (`Experiments/`) was
not carried over; it remains on the `cert` branch.
