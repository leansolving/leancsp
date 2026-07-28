# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2026-07-28

This release adds the unsatisfiability side of the project. LeanCSP could already model a
CSP and export it to a solver; it can now also prove a CSP unsatisfiable, with the result
checked by the Lean kernel rather than taken on the solver's word.

### Added

- Verified pseudo-Boolean backend (`CSP/L2S/Backends/PB/`, 22 modules). A finite-domain
  CSP is compiled to PB constraints through a Lean-verified order encoding, an external PB
  solver proves the result unsatisfiable, and the solver's proof is re-checked in the
  kernel to yield `¬ csp.isSatisfiableInt`. The solver and the proof elaborator are
  untrusted; a faulty proof makes the theorem fail to elaborate rather than go through.
- One general soundness theorem, `csp_sat_pb_sat`: every satisfiable `IntCSP` has a
  satisfiable PB encoding. `csp_unsat` is its contrapositive. Instances carry no soundness
  hypotheses of their own, so a new problem is one line plus a certificate file.
- `csp_unsat_file`, which loads a committed VeriPB certificate at compile time and
  discharges the reflection check with a `Lean.ofReduceBool` term. The axiom stays stable
  and nameable across theorems instead of becoming a fresh per-theorem `native_decide`
  axiom.
- Encoder coverage for all 51 `IntConstraint` constructors, with per-pattern soundness.
  Four carry no PB constraints, soundly: `bound` builds the domains, `disjunctive` and
  `unknown` have semantics `True`, and `product_rel_var` is non-linear and is dropped.
- 50 end-to-end UNSAT theorems over 50 committed certificates, covering pigeonhole, graph
  colouring, odd cycles, Schur, van der Waerden, Ramsey, Paley, Langford, Sudoku, Latin
  squares, magic hexagon, mutilated chessboards, N-Queens, peaceable armies, and four
  circuit verification problems.
- `csp_sat_file` (`CSP/L2S/Witness.lean`), the satisfiability counterpart. An external
  solver's witness is re-checked by kernel `decide`, so lower-bound theorems depend on no
  reflection axioms at all.
- `CSP/L2S/EndToEnd/`, which states results about the original CSP by transporting a
  certificate about a symmetry-broken variant back through a verified symmetry break.
  This includes the exact Schur numbers S(2) = 4 and S(3) = 13, each bracketed by a
  witness below and a certificate above, and the kernel-checked S(4) >= 44.
- Value precedence (Law-Lee) as a verified domain symmetry-breaking constraint, with the
  hypotheses discharged for graph colouring, Schur, Ramsey, van der Waerden and pigeonhole.
- Further symmetry-breaking and equivalence proofs: Schur, Sudoku, Latin square, matching,
  mutilated chessboard and Langford. `CSP/L2S/Proofs/` grows from 11 to 25 modules.
- `SchurReversalCounterexample.lean`, a cautionary example. The strict lexicographic
  reversal leader is a sound symmetry break for van der Waerden but not for ordinary
  Schur, and the backend certifies the false UNSAT claim that results.
- `experiments/`, a reproducible harness for three studies: proof length under cutting
  planes against resolution, the effect of symmetry breaking on solving and checking cost,
  and the exact Schur numbers. See `experiments/README.md`.
- Four more example problems, bringing `CSP/L2S/Tests/lean/` to 36.

### Changed

- `HomogeneousCSP` is now `IntCSP`, and constraint satisfaction is pattern-determined:
  `satisfiesConstraintInt c a := patternHolds c a`. A constraint's meaning is a function of
  its finite pattern rather than an opaque checker, which is what makes a single generic
  encoder possible. This is a breaking change for existing models.
- Lean 4.24.0-rc1 to 4.30.0, with Mathlib pinned to the matching release.
- Documentation consolidated into `README.md` and `experiments/README.md`.

### Removed

- The `Canonical` dependency, which was imported but never used.
- `CircuitTwinSymmetryBreaking.lean` and `ParityPathCSP.lean`.
- The older benchmarking harness under `CSP/L2S/Proofs/Experiments/`, replaced by
  `experiments/`.

## [0.1.0] - 2025-12-02

Initial release of LeanCSP.

### Added

- Core CSP formalization with equivalence, equisatisfiability, and symmetry-breaking proofs
- L2S (LeanToSolver) framework with 50+ constraint types
- MiniZinc and SMT-LIB backend code generation
- Verified symmetry breaking for N-Queens, Graph Coloring, and Latin Square
- Verified equivalence proofs for N-Queens and Graph Coloring formulations
- Circuit optimization theorems (Unreachable Input Elimination, Parity Path)
- 32 example problems
