# Proofs

Formal Lean 4 proofs for CSP symmetry breaking, formulation equivalence, value
precedence, and circuit optimization theorems.

## Proof Files

### Symmetry Breaking (SB)

Each file proves that a candidate constraint is a valid symmetry-breaking
constraint (domain or variable symmetry) and hence *equisatisfiable* with the
original CSP — the reduced problem is UNSAT iff the original is.

| File | Problem | Symmetry | Constraint |
|------|---------|----------|------------|
| `NQueensSB.lean` | N-Queens | Horizontal reflection `x ↦ (n-1)-x` (domain) | First queen in top half |
| `GraphColoringSB.lean` | Graph Coloring | Color swap `swap 0 c` (domain) | Node 0 has color 0 |
| `LatinSquareSB.lean` | Latin Square | Column value permutation (variable) | First row nondecreasing |
| `SudokuSB.lean` | Sudoku | Value swap `swap 0 v` (domain) | Cell (0,0) fixed to 0 |
| `SchurSB.lean` | Schur numbers | Color swap `swap 0 c` (domain) | `x₀ = 0` |
| `MatchingSB.lean` | Perfect matching / parity on `K_{2m+1}` | Vertex transposition (0 1) (variable) | Order the two swapped edge vars |
| `MutilatedSB.lean` | Mutilated `2k×2k` chessboard | Main-diagonal reflection (variable) | Order the two swapped domino vars |
| `LangfordSB.lean` | Langford `L(2,n)` | Sequence reversal `p ↦ 2n+1-p` (composite) | Digit-0 first copy in first half |

Representative theorems per file: `*_is_symmetry` (the map preserves
solutions), `*_is_..._symmetry_breaking` (the constraint is a valid SBC), and
`*_equisatisfiability` / `*_unsat_of_*` (the reduction preserves (UN)SAT).

### Equivalence Proofs

All use **π-equivalence**: an explicit projection `π` and lifting `λ` between the
two formulations, combined into a proof of `equivalent`. This transports both
solutions and UNSAT across the reformulation.

| File | Formulations | Method |
|------|--------------|--------|
| `NQueensEquivalence.lean` | Column model (var/column) ↔ board model (n² binary squares) | Projection/lifting between row-per-column and one-per-square |
| `GraphColoringEquivalence.lean` | Vertex model ↔ binary one-hot matrix | π extracts color from one-hot, λ builds one-hot |
| `LatinSquareEquivalence.lean` | Value-compact (n² cells) ↔ one-hot binary (n³ vars) | π finds the unique 1 per cell, λ one-hot encodes |
| `SudokuEquivalence.lean` | Value-compact ↔ one-hot expanded (adds box constraints) | Same projection/lifting as Latin square |
| `SchurEquivalence.lean` | Compact color model ↔ binary (integer,color) matrix | π extracts color, λ builds one-hot |
| `MutilatedEquivalence.lean` | Orientation model (U/D/L/R per cell) ↔ edge/exact-cover domino model | π-equivalence; coverage free (points-to = fixed-point-free involution) |

Key theorems per file: `*_pi_equivalent` and `*_equivalent` (plus
`mutilated_orient_unsat_of_edge_unsat`, which transports UNSAT into the
never-PB-encoded orientation model).

### Value Precedence

Each file discharges the two hypotheses of
`value_precedence_is_domain_symmetry_breaking`: (a) a domain bound `*_hdom`
(solutions land in `[0, colors-1]`) and (b) `*_interval_perm_is_symmetry`
(interval-preserving value permutations are domain symmetries). Together these
make `value_precedence colors` a valid domain-symmetry-breaking constraint for
the problem.

| File | Problem | Colors | Preservation lemma |
|------|---------|--------|--------------------|
| `GraphColoringValuePrecedence.lean` | Graph Coloring | `colors` | `not_equal` edges preserved by any permutation (injectivity) |
| `SchurValuePrecedence.lean` | Schur | `colors` | `schur_triple_preserved_by_perm` |
| `PigeonholeValuePrecedence.lean` | Pigeonhole (`php_sb`) | `holes` | `alldifferent_preserved_by_perm` |
| `RamseyValuePrecedence.lean` | Ramsey R(3,3) | 2 | not-all-equal triangle triples |
| `VanDerWaerdenValuePrecedence.lean` | Van der Waerden | 2 | not-all-equal over 3-APs |

### Circuit Theorems

| File | Result |
|------|--------|
| `CircuitInputSymmetryBreaking.lean` | Permuting fully-symmetric (identical-fanout) inputs is a variable symmetry; `increasing(symmetric_inputs)` is a valid SBC (AND/OR/XOR/at-most-k all preserved) |
| `UnreachableInputElimination.lean` | An input with no path to any output can be fixed to any value; base and modified CSPs are equisatisfiable |
| `ParityPathTheorem.lean` | Pure-literal rule for AND/OR/NOT circuits: an input whose paths to all outputs share one parity can be fixed to its optimal value (even→1, odd→0); XOR excluded |

Representative theorems: `input_permutation_is_variable_symmetry` /
`circuit_symmetry_breaking_equisatisfiable`; `unreachable_input_sat_equiv`;
`uniform_parity_pure_literal` / `uniform_parity_sat_equiv`.

### Problem-Specific Bridges

| File | Result |
|------|--------|
| `SchurColorable.lean` | Pure-math bridge `schur_csp_iff_colorable` connecting the Schur CSP to the textbook `SchurColorable n c` (sum-free c-coloring of `{1,…,n}`), so a checked witness yields a lower bound and a PB-UNSAT yields `¬SchurColorable (n+1) c` |

> ## Axiom status
>
> **This corpus is intended to be axiom-clean** — every theorem should reduce to
> only `propext, Classical.choice, Quot.sound`. Check any theorem with
> `#print axioms <name>`. No file contains `sorry` or a local `axiom`
> declaration. **New axioms must not be introduced into this corpus.**

### Shared Infrastructure

`PatternBridges.lean` provides the two-way `*_holds_iff` bridges from
`IntCSP.satisfiesConstraintInt` (= `patternHolds`) to the direct `Fin`-indexed
forms these proofs reason with (`alldifferent_holds_iff`,
`alldifferent_all_holds_iff`, `increasing_holds_iff`, `sum_eq_holds_iff`,
`toList_map_ofFn`, the N-Queens diagonal lemmas, …). It concentrates all
`valAt`/`dite` scope plumbing. The forward-only `*_sat` bridges in `Backends/PB/`
serve the UNSAT pipeline; the symmetry and equivalence proofs need *both*
directions because they transport solutions across permutations. Consumed by
`LatinSquareSB`, `NQueensSB`, `SchurSB`, `SudokuSB`, `LangfordSB`, and the
equivalence files.

## Instance Generation

Each problem file defines `IO` helpers that emit `.mzn` and `.smt2` problem
instances into `mzn/` and `smt2/` subdirectories (created on demand via
`Translate.translateTo` / `saveToAuto`), for external benchmarking of the
verified reformulations.

## Experiments

`Experiments/` holds the Python benchmarking harness (`run_experiments.py`,
`run_parity_experiments.py`, `verify_equivalence.py`, `profile_proofs.py`), the
`ParityCircuitBenchmarks.lean` circuit-instance generator (ported to the current
`IntCSP` API), and committed result CSVs. The scripts consume the generated
`.mzn`/`.smt2` instances and run external solvers (MiniZinc/Gecode/Chuffed,
Z3, CVC5). See `Experiments/README.md`. The committed result CSVs are historical
(from the original run); regenerate them by re-running the scripts with the
solvers installed.
