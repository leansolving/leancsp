# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- **Strict reversal lex leader constraint** `IntConstraint.strictLexRevLeader`
  (`x <_lex rev x`), wired through `patternHolds`, the MiniZinc/SMT-LIB translators,
  and the verified PB backend: `PB/LexLeader.lean` encodes it over `{0,1,2}` domains as
  the single Big-M base-3 mirror disequality `Σ (3ⁱ − 3^{rev i})·xᵢ ≠ 0` (a sound
  relaxation, `0` iff `x` is a palindrome), with a base-3 non-vanishing soundness lemma.
- **Schur cautionary example** (`Proofs/SchurReversalCounterexample.lean`,
  `Problems/SchurLexLeader.lean`): `schur_leader_not_variableSBC` proves the strict
  reversal leader is *not* a valid `variableSymmetryBreakingConstraint` on the 3-colour
  Schur CSP at `n = 13` — base CSP SAT (`csp_sat_file` witness) but augmented CSP UNSAT
  (kernel-checked PB certificate `certs/schur_lex_13.pbp`), breaking equisatisfiability.
  Plus reformulation-level, `decide`-only companions (`reversal_not_schur_symmetry`).

### Changed

- **UNSAT discharge migrated to `Lean.ofReduceBool`.** `csp_unsat_file` is now a term
  elaborator (`cspUnsatReflect`) that builds the PBLean reflection proof as a hand-rolled
  `Lean.ofReduceBool` term instead of the `native_decide` tactic. Call sites are
  unchanged, but every committed UNSAT theorem now carries the stable, nameable
  `Lean.ofReduceBool` / `Lean.trustCompiler` axioms rather than a fresh per-theorem
  `._native.native_decide.ax`. (SAT-witness lower bounds via `csp_sat_file` are
  unaffected — still kernel `decide`, `native_decide`-free.)

### Added (earlier)

- **Single generic UNSAT theorem** `csp_unsat csp cert : ¬ csp.isSatisfiableInt`
  (`PB/GenericEncode.lean`): derives the order-encoding signature, the PB formula,
  and all soundness preconditions from the CSP automatically — no per-instance proof.
- `encodePattern` / `encodePattern_sound` — generic per-constraint encoding +
  soundness over the `IntConstraint` inductive (covers `bound`, `alldifferent`,
  `not_equal`/`eq_const`/`ne_const`, `at_most_k`/`at_least_k`, `linear`, `sum`,
  `schur_triple`), each feeding the per-pattern library soundness lemma.
- `EncConstr` composition spine (`PB/Compose.lean`) with an automatic aux-index
  allocator, and the per-pattern `enc*` library (`PB/Library.lean`).
- File-based certificates: `csp_unsat_file` macro (`include_str` + `native_decide`)
  loading committed `Problems/certs/*.pbp`, and `experiments/gen_cert.py` to regenerate
  them against the canonical encoder (RoundingSat + veripb).

### Changed

- **`Int` nomenclature.** `HomogeneousCSP` → `IntCSP`, `HomogeneousConstraint`/tagged
  representation → the `IntConstraint` inductive; satisfaction is now
  pattern-determined (`satisfiesConstraintInt c a := patternHolds c a`).
  `isSolution`/`isSatisfiable` → `isSolutionInt`/`isSatisfiableInt`.
- 22 corpus UNSAT theorems rewritten from bespoke hand-written proofs to one-line
  `csp_unsat_file` over committed certificates; instance modules moved to
  `CSP/L2S/Backends/PB/Problems/`.

### Removed

- `CSP/L2S/Proofs/` (equivalence + symmetry-breaking experiments not part of the
  verified PB UNSAT pipeline).

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
