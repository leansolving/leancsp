# CSP: A Formalization in Lean of Constraint Satisfaction Problems

This Lean 4 + Mathlib project formalizes Constraint Satisfaction Problems (CSPs). It has two halves that share one modeling layer:

1. **L2S (LeanToSolver)** — model a CSP once in Lean and export it to **MiniZinc** / **SMT-LIB** for solving.
2. **A verified pseudo-Boolean (PB) UNSAT-certificate backend** — compile a finite-domain CSP to PB constraints through a *Lean-verified* order encoding, then turn an external solver's UNSAT proof into a **kernel-checked Lean theorem** `¬ csp.isSatisfiableInt`. The external SAT/PB solver and proof elaborator are untrusted oracles; only the encoder and the proof checker are trusted, and both are verified in Lean.

The PB backend is the focus of this branch; it is described first below.

---

## Verified UNSAT certificates (the PB backend)

`CSP/L2S/Backends/PB/` (namespace `CSP.L2S.PB`) produces, for a finite-domain CSP, a Lean theorem

```lean
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiableInt :=
  csp_unsat_file php_3_2 3 "certs/php_3_2.pbp"
```

where `php_3_2` is a genuine corpus CSP (three pigeons into two holes). The theorem is checked by Lean's kernel; no UNSAT verdict is taken on faith.

### One generic soundness theorem, applied in one line

The heart of the backend is a **single generic theorem** (`GenericEncode.lean`):

```lean
theorem csp_unsat (csp : IntCSP)
    (cert : VeriPB.Reflect.formulaUnsat
      (((cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)).toArray.map
        PBConstr.toNatConstr))
    (hbound : … := by decide) :
    ¬ csp.isSatisfiableInt
```

It says, once and for all: *if the canonical PB encoding of `csp` is UNSAT (kernel-checked certificate), then `csp` is unsatisfiable.* Everything is derived from the CSP automatically — the order-encoding signature `cspSig csp` from its `bound` constraints, the PB formula `encodeCSP csp` by dispatching each `IntConstraint` to its verified per-pattern encoder, and the in-domain / per-constraint preconditions from the constraint semantics (`patternHolds`).

The `csp_unsat_file csp numVars "certs/foo.pbp"` macro is `csp_unsat` with the certificate loaded from a committed `.pbp` file at compile time (`include_str`) and re-checked by PBLean via `native_decide`.

**This replaces the old per-problem hand-written Lean proofs.** Previously each instance carried its own `CSPSig`, hand-rolled encoding, per-constraint soundness bridges, and a multi-step `csp_unsat_generic` assembly (tens to hundreds of lines). Now every supported instance is **one line plus a certificate file**; adding a new constraint family means adding one `encodePattern` case and one `encodePattern_sound` case — never per-problem proof work.

### The pipeline

```
IntCSP  (Lean; e.g. the corpus CSP php_3_2)
   │
   │  encodeCSP — VERIFIED IN LEAN: dispatch each IntConstraint to its
   │  per-pattern order encoder; integer var x with domain D ↦ threshold bits "x ≤ dⱼ"
   ▼
PB constraints over typed threshold variables  (EncConstr / PBVar)
   │
   │  toNat injection  →  PBLean's Sat.PB.Constr   (VERIFIED IN LEAN)
   ▼
OPB file  ──[ RoundingSat, UNTRUSTED ]──▶  VeriPB proof
                                              │
                                              │  [ veripb --elaborate, UNTRUSTED ]
                                              ▼
                                  kernel proof  (committed as Problems/certs/<name>.pbp,
                                                 loaded via include_str)
   │
   │  PBLean reflection checker  checkProof_sound  (VERIFIED IN LEAN; run by native_decide)
   ▼
formulaUnsat  ──[ csp_unsat soundness theorem ]──▶  ¬ csp.isSatisfiableInt   (kernel-checked)
```

Generating a certificate for a new instance is one script call:

```bash
scripts/gen_cert.sh <Module> <cspExpr> <out>     # dumps OPB, runs RoundingSat + veripb,
                                                 # commits Problems/certs/<out>.pbp, prints numVars
```

Re-checking a *committed* theorem needs **only Lean + the Mathlib cache** — RoundingSat and veripb are not required.

### The `Int` nomenclature

The modeling type for the PB backend is `IntCSP` (`CSP/L2S/Core.lean`): a number of integer variables (`num_vars`) and a `List (IntConstraint num_vars)`. The constraint inductive `IntConstraint` enumerates every available constraint (50+ constructors). Satisfaction is **pattern-determined**: `IntCSP.satisfiesConstraintInt c a := patternHolds c a`, where `patternHolds` gives each constructor its arithmetic meaning. This is what makes a *generic* encoder possible — `encodePattern` reads the finite constructor and `encodePattern_sound` derives the encoder's precondition straight from `patternHolds`, with no opaque per-constraint checker in the way.

The corresponding predicates are `isSolutionInt` and `isSatisfiableInt`. (The names mirror the `IntCSP`/`IntDomain`/`VarType`/`IntAssignment` family throughout `CSP/L2S/`.)

### The Lean-side modules

| Module | Role |
|--------|------|
| `PB/CSPSig.lean`, `PB/PBVar.lean` | The encoder's variable signature and typed threshold-variable type (`thr i j` ≡ "integer var `i` is ≤ its `j`-th domain value"). |
| `PB/Semantics.lean` | `intValue` (recover the integer from the threshold bits), `monotonicity` (staircase clauses), `intValue_mem_values`. |
| `PB/Substitution.lean` | `linear_le_of_threshold_sum` — a linear constraint over CSP variables becomes a linear PB constraint over threshold bits. |
| `PB/SignedPB.lean`, `PB/Encode.lean` | Signed→natural PB normalization and `encodeLinearLe` (+ soundness), the base every linear encoder builds on. |
| `PB/AllDifferent.lean`, `PB/Cardinality.lean`, `PB/LinearNe.lean`, `PB/NotAllEqual.lean`, `PB/BoolGates.lean` | The per-family encoders, each with a Lean soundness lemma. |
| `PB/ToNat.lean` | Injects typed `PBVar` into `Nat`, maps to PBLean's `Sat.PB.Constr`, proves `unsat_bridge`. |
| `PB/Extend.lean` | The order-encoding spine `csp_unsat_generic`: "every CSP solution extends to a PB model" + a certificate ⇒ `¬ ∃ solution`. |
| `PB/Compose.lean` | `EncConstr` (a soundness-carrying encoded constraint) and the assumption-free composition `csp_unsat_of_enc` / `csp_unsat_of_enc_alloc` (with an automatic aux-index allocator). |
| `PB/Library.lean` | One `enc<Pattern>` smart constructor per supported family, each bundling its encoding with its per-constraint soundness (reusing the `extend_sat_*` lemmas). |
| **`PB/GenericEncode.lean`** | **`cspSig`, `encodePattern` (`IntConstraint` → `EncConstr` list), `encodePattern_sound`, `encodeCSP`, and the single generic theorem `csp_unsat` + the `csp_unsat_file` macro.** |
| `PB/Adapter.lean`, `PB/NotAllEqualBridge.lean` | Domain-value lists, `bound_sat`, and the per-pattern `*_sat` bridges reused by the encoders. |
| `PB/Tactic.lean` | The older `csp_reflect_unsat` command (reads a `.pbp` and discharges `formulaUnsat`) and `csp_decide` (shells out at elaboration time, non-hermetic). `csp_unsat_file` is the preferred form. |

### Trust boundary

**Trusted:** Lean's kernel; PBLean's PB proof checker (its soundness `checkProof_sound` is proved in Lean, *run* by `native_decide`, which places the Lean compiler in the trusted base via `Lean.ofReduceBool` — the same trust shape as `bv_decide`); this backend's order-encoder and `encodePattern` soundness theorems (verified in Lean).

**Untrusted** (a fault is *caught*, never certifies a false theorem): RoundingSat, veripb, and the OPB serializer. If the on-disk OPB or proof doesn't match the Lean-side PB formula, `checkProof_sound`'s hypothesis fails to discharge and the theorem does not go through.

Every end-to-end theorem depends (`#print axioms`) on exactly:

```
propext,  Classical.choice,  Quot.sound,  <theorem>._native.native_decide.ax_1_1
```

— the three standard axioms plus **one** `native_decide` axiom (the kernel-checked certificate). No `sorryAx`.

### Supported constraint fragment

The generic encoder (`encodePattern`) currently covers, **fully automatically via `csp_unsat`**:

`bound` (domains) · `alldifferent` · `not_equal` / `eq_const` / `ne_const` · cardinality `at_most_k` / `at_least_k` · `linear` (`≤, ≥, <, >, =`) · `sum` (`≤, ≥, <, >, =`) · `schur_triple` (not-all-equal).

Constraint families with an existing encoder but not yet wired into `encodePattern` (still handled by older bespoke proofs, see the table): `alldifferentOffset` (diagonal all-different), Boolean gates (`and_gate`/`or_gate`/`not_gate`/`xor_*`/`and_all`/`or_all`), and the Big-M general linear `≠` (`linear_ne`, which needs an auxiliary variable). See **Next steps**.

### End-to-end UNSAT theorems

Each row is a kernel-checked `¬ ....isSatisfiableInt` theorem for a CSP from (or built on) `CSP/L2S/Tests/lean/`. All are axiom-clean as above. The first group is **one-line `csp_unsat_file`** over a committed certificate; the second still uses a bespoke proof pending its encoder being wired into `encodePattern`.

**Generic (`csp_unsat_file`, one line + `Problems/certs/*.pbp`):**

| Theorem | Module | What it certifies |
|---------|--------|-------------------|
| `php_3_2`/`5_4`/`7_6`/`9_8_unsat` | `Pigeonhole.lean` | `k+1` pigeons cannot injectively occupy `k` holes (`alldifferent`). |
| `k3_2col_unsat` | `GraphColoring.lean` | The triangle K₃ is not 2-colourable. |
| `k4_3col_unsat` | `GraphColoring.lean` | K₄ is not 3-colourable. |
| `c5`/`c7`/`c9_2col_unsat` | `OddCycle.lean` | The odd cycles C₅/C₇/C₉ are not 2-colourable. |
| `k2_forbidden_unsat` | `ForbiddenColoring.lean` | K₂ with colour 1 forbidden at both endpoints is uncolourable. |
| `schur_2_5_unsat` | `Schur.lean` | `{1..5}` has no sum-free 2-colouring (S(2)=4). |
| `schur_3_14_unsat` | `Schur3.lean` | `{1..14}` has no sum-free 3-colouring (S(3)=13). |
| `vdw_2_3_9_unsat` | `VanDerWaerden.lean` | No 2-colouring of `{1..9}` avoids a mono 3-AP (W(2,3)=9). |
| `ramsey_3_3_K6_unsat` | `Ramsey.lean` | Every 2-colouring of K₆'s edges has a mono triangle (R(3,3)=6). |
| `paley_13_4_unsat` | `Paley.lean` | α(Paley(13)) ≤ 3 (no independent set of size 4). |
| `langford_2_2_unsat` | `Langford.lean` | Langford pairing L(2,2) has no solution. |
| `sudoku_4_contradictory_unsat` | `Sudoku.lean` | A 4×4 Sudoku with two equal row-0 givens is unsolvable. |
| `latin_2_contradictory_unsat` | `Latin.lean` | A binary-encoded order-2 Latin square with contradictory givens is unsolvable. |
| `magic_hexagon_2_unsat` | `MagicHexagon.lean` | No order-2 normal magic hexagon (forced line sum `28/3`). |
| `mutilated_chessboard`/`_6_unsat` | `MutilatedChessboard*.lean` | A 4×4 / 6×6 board minus two same-colour corners has no domino tiling. |
| `peaceable_armies_4_3_unsat` | `PeaceableArmies.lean` | No 3+3 peaceable queens on a 4×4 board (a(4)=2). |

**Bespoke (pending `encodePattern` coverage — see Next steps):**

| Theorem | Module | Missing family |
|---------|--------|----------------|
| `nqueens_2`/`nqueens_3_unsat` | `NQueens.lean` | `alldifferentOffset` (diagonals) |
| `blocked_queens_4_unsat` | `BlockedQueens.lean` | `alldifferentOffset` |
| `xor_equivalence_unsat` | `CircuitEquiv.lean` | Boolean gates |
| `circuit_majority3_unsat` | `Circuit.lean` | Boolean gates |
| `full_adder_correct_unsat` | `FullAdder.lean` | gates + `linear_ne` (aux) |
| `ripple_carry_4bit_correct_unsat` | `RippleCarry.lean` | `linear_ne` (aux) |

Corpus instances live under `CSP/L2S/Backends/PB/Problems/`; the reusable backend (encoders, `Compose`/`Library`/`GenericEncode`, and the `Demo*` tutorials) stays in `CSP/L2S/Backends/PB/`.

### Build and verify

```bash
lake exe cache get     # pre-built Mathlib oleans (avoids a 30+ min build)
lake build             # compiles EVERYTHING, including every UNSAT theorem above
```

A clean `lake build` **is** the verification: the lakefile uses `globs := #[.andSubmodules `CSP]`, so a bare build compiles the CSP root and all submodules, re-checking every embedded certificate via `native_decide`.

```bash
# verify one instance and inspect its trust boundary
lake build CSP.L2S.Backends.PB.Problems.Pigeonhole
echo 'import CSP.L2S.Backends.PB.Problems.Pigeonhole
#print axioms CSP.L2S.PB.Pigeonhole.php_3_2_unsat' > /tmp/chk.lean
lake env lean /tmp/chk.lean
```

### Adding a new UNSAT instance

For a CSP built only from the supported fragment, the whole instance is:

```lean
import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«NN_my_problem»     -- the corpus CSP

namespace CSP.L2S.PB.MyProblem
open CSP.L2S CSP.L2S.PB

theorem my_unsat : ¬ myCSP.isSatisfiableInt :=
  csp_unsat_file myCSP <numVars> "certs/my.pbp"
end CSP.L2S.PB.MyProblem
```

and `scripts/gen_cert.sh CSP.L2S.Tests.lean.«NN_my_problem» myCSP my` produces `numVars` and the committed `certs/my.pbp`. The full playbook is in **[`docs/ADDING_UNSAT_INSTANCES.md`](docs/ADDING_UNSAT_INSTANCES.md)**; the architecture and implemented-status summary are in **[`PLAN.md`](PLAN.md)**.

### Next steps — covering all constraints and problems

The end goal is for **every** finite-domain CSP in the supported modeling fragment to be discharged by the one-line `csp_unsat_file`. The remaining work is all in `encodePattern` / the encoder library (never per-problem):

1. **`alldifferentOffset`** (diagonal all-different, for N-Queens / blocked queens) — add an offset-aware all-different encoder `encodeAllDifferentOffset` (per-value cardinality on the shifted values `a vᵢ + offsetᵢ`) with its soundness lemma, then one `encodePattern` case. Migrates `nqueens_*`, `blocked_queens_4`.
2. **Boolean gates** (`and_gate`/`or_gate`/`not_gate`/`xor_*`/`and_all`/`or_all`) — emit the linear `{0,1}` encodings (`out ≤ inᵢ`, `out ≥ Σ inᵢ − (k−1)`, parity via the full-adder identity) as `EncConstr`s and derive their preconditions from `patternHolds`. Migrates the circuit family (`xor_equivalence`, `circuit_majority3`).
3. **Big-M general linear `≠`** (`linear_ne`) — wire `encLinearNe` (which owns one auxiliary selector) into `encodePattern`, switching `csp_unsat` from the aux-free `csp_unsat_of_encfree` spine to `csp_unsat_of_enc_alloc` and sizing `cspSig`'s `nAux` to the number of `≠` constraints (the allocator already builds the global aux assignment from pairwise-distinct owned indices). Migrates `full_adder`, `ripple_carry`.
4. **The remaining `IntConstraint` constructors** (`count`, `element`, `maximum`/`minimum`, `modulo`, `abs_diff_*`, `increasing`, `implies`/`iff`, `*_rel_var`, …) — each becomes one `encodePattern` case + soundness over an encoder; unsupported/non-linear ones (e.g. `product_rel_var`) stay `[]` (sound by weakening).
5. **Scaling** — larger corpus sizes and a regeneration sweep (`scripts/gen_cert.sh` over all instances) once an encoder changes shape.

Each item is local: an encoder + its soundness lemma + a single `encodePattern`/`encodePattern_sound` case, after which the instances collapse to one-liners with regenerated certificates.

---

## Project Structure

```
CSP/
├── Core.lean                 # General heterogeneous CSP definitions
├── Symmetry.lean             # General symmetry theory
├── Equivalence.lean          # General equivalence theory
├── GlobalConstraints.lean    # Predefined constraints
├── Transport.lean            # Type casting utilities
│
└── L2S/                      # LeanToSolver framework
    ├── Core.lean             # IntCSP / IntConstraint / patternHolds foundations
    ├── Constraints.lean      # 50+ constraint smart constructors
    ├── Translate.lean        # Unified translation API
    ├── Backend.lean          # Backend interface + translateWith driver
    ├── Backends/
    │   ├── MiniZinc.lean     # MiniZinc code generation
    │   ├── SMTLIB.lean       # SMT-LIB code generation
    │   └── PB/               # Verified pseudo-Boolean UNSAT backend (above)
    │       ├── GenericEncode.lean   # cspSig, encodePattern, csp_unsat, csp_unsat_file
    │       ├── Compose.lean / Library.lean   # EncConstr spine + per-pattern library
    │       └── Problems/     # Corpus instances (one-liners) + certs/*.pbp
    ├── Embedding.lean        # Embedding into the heterogeneous CSP
    └── Tests/lean/           # Example problems (also instance generators)

scripts/gen_cert.sh           # regenerate a certificate against the canonical encodeCSP
```

## Requirements

| Tool | Purpose | Link |
|------|---------|------|
| **Lean 4 + elan** | Theorem prover (required) | [lean-lang.org/install](https://lean-lang.org/install/) |
| **MiniZinc** | Constraint solver for the translation backend (optional) | [minizinc.org](https://www.minizinc.org/downloads/) |
| **Z3 / CVC5** | SMT solvers for the translation backend (optional) | [z3](https://github.com/Z3Prover/z3/releases) / [cvc5](https://github.com/cvc5/cvc5/releases) |
| **RoundingSat** | PB solver — only to *generate* a new UNSAT certificate (optional) | [gitlab.com/MIAOresearch/software/roundingsat](https://gitlab.com/MIAOresearch/software/roundingsat) |
| **veripb** | PB proof elaborator — only to *generate* a new certificate (optional) | [gitlab.com/MIAOresearch/software/VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) |

The Lean dependency **PBLean** (providing `VeriPB.Reflect.checkProof_sound`) is fetched automatically by Lake (pinned in `lake-manifest.json`).

Install [elan](https://lean-lang.org/install/manual/) so the pinned Lean version is fetched automatically:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source $HOME/.elan/env
```

## Building the Project

```bash
git clone https://github.com/leansolving/leancsp.git
cd leancsp
lake exe cache get     # pre-built Mathlib cache (saves 30+ min)
lake build             # builds root + all submodules
```

To re-check a single module once its imports are built: `lake env lean <path/to/File.lean>`.

## Usage

### Modelling CSPs

The L2S framework uses `IntCSP` — a number of integer variables and a list of `IntConstraint`s:

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

def graph_coloring (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : IntCSP :=
  let bounds := (List.finRange nodes).map fun v => bound v 1 colors
  let edge_constrs := edges.map fun (u, v) => not_equal u v
  ⟨nodes, bounds ++ edge_constrs⟩
```

Available constraints: `alldifferent`, `count`, `element`, `sum_eq`, `linear_eq`, `not_equal`, `at_most_k`, `at_least_k`, `bound`, and 40+ more (see `L2S/Constraints.lean` and `L2S/README.md`).

> **Bounds are constraints, not domains.** A variable's range comes from a `bound v lb ub` constraint. During translation these become solver variable declarations; a variable with no `bound` defaults to `[-1000, 1000]`. The PB backend's `cspSig` reads exactly these bounds.

### Solver translation (MiniZinc / SMT-LIB)

```lean
import CSP.L2S.Translate
open CSP.L2S

def my_csp : IntCSP := ...

def main : IO Unit := do
  saveTo my_csp "model.mzn" BackendType.MiniZinc
  saveTo my_csp "model.smt2" BackendType.SMTLIB
```

```bash
lake env lean --run MyFile.lean   # runs `main`, emits the files
minizinc model.mzn                # or: z3 model.smt2  /  cvc5 model.smt2
```

## Main Definitions

### CSP Equivalence

Two CSPs are equivalent if there is a bijection between their solution sets:

```lean
def equivalent (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) : Prop :=
  ∃ f : {x // x ∈ sol_set csp₁} → {x // x ∈ sol_set csp₂}, Function.Bijective f
```

### CSP Equisatisfiability

```lean
def equisatisfiable (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) : Prop :=
  is_satisfiable csp₁ ↔ is_satisfiable csp₂
```
