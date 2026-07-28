# LeanCSP

[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4.30.0-blue.svg)](lean-toolchain)

A Lean 4 + Mathlib formalization of Constraint Satisfaction Problems. You model a CSP once in
Lean and can then either export it to MiniZinc or SMT-LIB for solving, or prove it
unsatisfiable. The unsatisfiability proof compiles the CSP to pseudo-Boolean constraints
through a Lean-verified order encoding, runs an external PB solver, and turns the solver's
UNSAT proof into a kernel-checked theorem `¬ csp.isSatisfiableInt`. The solver and the proof
elaborator are untrusted; only the encoder and the proof checker are trusted, and both are
verified in Lean.

The project also proves that candidate symmetry-breaking constraints are sound and that
alternative formulations of a problem are equivalent. This is what lets a certificate about a
reduced model transport back to the original problem.

## Requirements

- [elan](https://lean-lang.org/install/manual/) manages the Lean and Mathlib versions pinned
  by the project. Install it before anything else:
  ```bash
  curl https://elan.lean-lang.org/elan-init.sh -sSf | sh && source $HOME/.elan/env
  ```
- MiniZinc, Z3 or cvc5 (optional) to solve the models that L2S exports.
- RoundingSat and veripb (optional). These are only needed to generate a new certificate.
  Re-checking the committed ones requires nothing but Lean.

PBLean, which provides the verified VeriPB proof checker, is fetched automatically by Lake.

## Build

```bash
git clone https://github.com/leansolving/leancsp.git
cd leancsp
lake exe cache get   # download prebuilt Mathlib (saves 30+ min)
lake build
```

A clean `lake build` is the verification. The lakefile globs every submodule, so a bare build
compiles the whole project and re-checks every committed certificate.

## Usage

### Modelling a CSP

An `IntCSP` is a variable count together with a list of `IntConstraint`s. A variable's range
comes from a `bound` constraint, so bounds are constraints rather than a separate domain
field.

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

def graph_coloring (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : IntCSP :=
  let bounds := (List.finRange nodes).map fun v => bound v 1 colors
  let edge_constrs := edges.map fun (u, v) => not_equal u v
  ⟨nodes, bounds ++ edge_constrs⟩
```

There are 51 constraints available, including `alldifferent`, `count`, `element`, `sum_eq`,
`linear_eq`, `at_most_k` and the Boolean gates. See `CSP/L2S/Constraints.lean`.

### Exporting to a solver

```lean
import CSP.L2S.Translate
open CSP.L2S

def main : IO Unit := do
  saveTo my_csp "model.mzn" BackendType.MiniZinc
  saveTo my_csp "model.smt2" BackendType.SMTLIB
```

```bash
lake env lean --run MyFile.lean   # runs `main`, emits the files
minizinc model.mzn                # or: z3 model.smt2  /  cvc5 model.smt2
```

### Proving a CSP unsatisfiable

Every committed instance is one line plus a certificate file:

```lean
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiableInt :=
  csp_unsat_file php_3_2 3 "certs/php_3_2.pbp"
```

`csp_unsat_file csp numVars "certs/foo.pbp"` loads a VeriPB kernel proof at compile time and
re-checks it. The order-encoding signature, the PB formula and every precondition are all
derived from `csp` automatically. The `numVars` argument is printed by
`experiments/gen_cert.py` when it generates the certificate.

## How it works

```
IntCSP ──encodeCSP──▶ PB constraints ──▶ OPB file ──[ RoundingSat ]──▶ VeriPB proof
        (verified)      over threshold                                      │
                          variables                          [ veripb --elaborate ]
                                                                            ▼
   ¬ csp.isSatisfiableInt  ◀──[ csp_unsat ]── formulaUnsat ◀──[ checker ]── certs/*.pbp
        (kernel-checked)                                       (verified)
```

1. **Encode.** `encodeCSP` dispatches each `IntConstraint` to its per-pattern order encoder.
   An integer variable with domain `D` becomes threshold bits "`x ≤ dⱼ`".
2. **Solve.** The PB constraints are serialized to OPB, RoundingSat solves them, and veripb
   elaborates its log into a kernel certificate committed under `Problems/certs/`.
3. **Check.** PBLean's reflection checker re-runs the certificate against the Lean-side
   formula, and `csp_unsat` turns the resulting `formulaUnsat` into `¬ csp.isSatisfiableInt`.

The whole backend rests on one soundness theorem, `csp_sat_pb_sat`: every satisfiable
`IntCSP` has a satisfiable PB encoding. Its witness order-encodes the solution and sets the
Big-M selector auxiliaries with a generic allocator. Selector distinctness is proved once and
structurally, so no instance carries its own hypotheses. `csp_unsat` is the contrapositive.
Supporting a new constraint family takes one `encodePatternAt` case and one soundness case,
and no per-problem proof work.

All 51 `IntConstraint` constructors are handled. Four of them carry no PB constraints, and in
each case that is sound. `bound` is consumed by the signature to build the domains.
`disjunctive` and `unknown` have semantics `True`, so the empty encoding is exact.
`product_rel_var` is genuinely non-linear and is dropped, which is sound but incomplete.
`xor_all` is exact at arity 2 and 3; wider parity should be modelled as a chain of ternary
gates, as the corpus adders do.

### Trust boundary

Trusted: Lean's kernel, PBLean's proof checker, and this backend's encoder and soundness
theorems. The checker is proved sound in Lean, but its `Bool` check is run natively via
`Lean.ofReduceBool`, which puts the Lean compiler in the trusted base. This is the same trust
shape as `native_decide`.

Untrusted: RoundingSat, veripb, and the OPB serializer. A fault in any of them is caught
rather than certifying a false theorem. If the proof on disk does not match the Lean-side
formula, the check fails and the theorem does not elaborate.

Every UNSAT theorem depends on exactly `propext`, `Classical.choice`, `Quot.sound`,
`Lean.ofReduceBool` and `Lean.trustCompiler`. That is the three standard axioms plus the two
reflection axioms, which stay stable and nameable instead of becoming a fresh per-theorem
`native_decide` axiom. There is no `sorryAx` anywhere. SAT witnesses go through
`csp_sat_file`, which uses kernel `decide` and needs neither reflection axiom. You can check
this yourself:

```bash
echo 'import CSP.L2S.Backends.PB.Problems.Pigeonhole
#print axioms CSP.L2S.PB.Pigeonhole.php_3_2_unsat' > /tmp/chk.lean
lake env lean /tmp/chk.lean
```

## Project structure

```
CSP/
├── Core.lean, Symmetry.lean, Equivalence.lean   # General heterogeneous CSP theory
├── GlobalConstraints.lean, Transport.lean
└── L2S/                          # LeanToSolver framework
    ├── Core.lean                 # IntCSP / IntConstraint / patternHolds
    ├── Constraints.lean          # The constraint constructors
    ├── Translate.lean            # Unified translation API
    ├── Witness.lean              # csp_sat_file, kernel-checked SAT witnesses
    ├── Backends/
    │   ├── MiniZinc.lean, SMTLIB.lean
    │   └── PB/                   # Verified pseudo-Boolean UNSAT backend
    │       ├── GenericEncode.lean    # cspSig, encodePattern, csp_unsat_file
    │       └── Problems/             # Corpus instances + certs/*.pbp
    ├── Proofs/                   # Symmetry breaking, equivalence, circuit theorems
    ├── EndToEnd/                 # Results about the original CSPs, via an SBC
    └── Tests/lean/               # Example problems
experiments/                      # Reproducible studies, see experiments/README.md
```

## Verified results

Each row is a kernel-checked `¬ ....isSatisfiableInt` theorem in
`CSP/L2S/Backends/PB/Problems/`. The `*SBC.lean` and `*VP.lean` modules carry the same
families extended with a symmetry-breaking constraint.

| Family | Certifies |
|---|---|
| Pigeonhole (`php_3_2` to `php_9_8`) | `k+1` pigeons cannot injectively occupy `k` holes |
| Graph colouring, odd cycles | K₃ and K₄ are not 2- resp. 3-colourable, nor are C₅, C₇, C₉ |
| Schur (`schur_2_5`, `schur_3_14`) | S(2) = 4 and S(3) = 13 |
| van der Waerden, Ramsey | W(2,3) = 9 and R(3,3) = 6 |
| Paley, Langford | α(Paley(13)) ≤ 3, and L(2,2) has no solution |
| Sudoku, Latin square, magic hexagon | Contradictory-given instances are unsolvable |
| Mutilated chessboard (4×4, 6×6) | A board minus two same-colour corners has no domino tiling |
| N-Queens, blocked queens, peaceable armies | No solution at the given sizes |
| Circuits (XOR equivalence, majority-3, full adder, ripple-carry) | Gate-level implementations meet their specifications |

`CSP/L2S/EndToEnd/` states results about the original CSP by transporting a certificate about
a symmetry-broken variant back through a verified SBC. `SchurCertify.lean` brackets each
Schur number from both sides, with a MiniZinc witness below and a PB certificate above, which
pins `S(2) = 4` and `S(3) = 13` exactly. `S(4) ≥ 44` is kernel-checked. Its upper bound needs
a certificate of about 98 MB that is too large to commit, so that block ships disabled. See
`experiments/README.md` for how to regenerate and enable it.

`CSP/L2S/Proofs/` holds the supporting theory: symmetry breaking (`NQueensSB`,
`GraphColoringSB`, `LatinSquareSB`, `SudokuSB`, `SchurSB`, `MatchingSB`, `MutilatedSB`,
`LangfordSB`), value precedence, π-equivalence between formulations, and circuit
optimization. `SchurReversalCounterexample.lean` is the cautionary counterpart. The strict
lexicographic reversal leader is a sound symmetry break for van der Waerden but not for
ordinary Schur, and the backend certifies the false UNSAT claim that results.

## Adding a new UNSAT instance

```lean
import CSP.L2S.Backends.PB.GenericEncode

theorem my_unsat : ¬ myCSP.isSatisfiableInt :=
  csp_unsat_file myCSP <numVars> "certs/my.pbp"
```

Generate the certificate and its `numVars` with the following, which needs `roundingsat` and
`veripb` on `PATH`:

```bash
python3 experiments/gen_cert.py <Module> <cspExpr> <out>
```

## Experiments

`experiments/` reproduces the proof-size scaling study, the symmetry-breaking study, and the
exact Schur numbers. See [`experiments/README.md`](experiments/README.md).

## License

Apache 2.0, see [LICENSE](LICENSE).
