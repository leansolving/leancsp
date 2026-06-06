# CSP: A Formalization in Lean of Constraint Satisfaction Problems

This Lean 4 + Mathlib project formalizes Constraint Satisfaction Problems (CSPs). It has two halves that share one modeling layer:

1. **L2S (LeanToSolver)** — model a CSP once in Lean and either reason about it (proofs of equivalence, equisatisfiability, symmetry-breaking) or export it to **MiniZinc** / **SMT-LIB** for solving.
2. **A verified pseudo-Boolean (PB) UNSAT-certificate backend** — compile a finite-domain CSP to PB constraints through a *Lean-verified* order encoding, then turn an external solver's UNSAT proof into a **kernel-checked Lean theorem** `¬ csp.isSatisfiable`. The external SAT/PB solver and proof elaborator are untrusted oracles; only the encoder and the proof checker are trusted, and both are verified in Lean.

The PB backend is the focus of this branch; it is described first below.

---

## Verified UNSAT certificates (the PB backend)

`CSP/L2S/Backends/PB/` (namespace `CSP.L2S.PB`) produces, for a finite-domain CSP, a Lean theorem of the form

```lean
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiable
```

where `php_3_2` is a genuine corpus CSP (here: three pigeons into two holes). The theorem is checked by Lean's kernel; no UNSAT verdict is taken on faith.

### Why this is interesting

Most "verified CSP" pipelines either trust the back-end solver (MiniZinc/SMT) or formalize one problem's encoding by hand. This backend is a **generic, verified compiler** from the modeling layer to pseudo-Boolean constraints, composed with a verified PB proof checker. Any CSP expressed in the supported fragment yields a kernel-checked UNSAT certificate without writing encoding-specific proofs, and PB (cutting-planes) targets give short proofs for counting-heavy problems (pigeonhole, Ramsey, independent set) where CNF/SAT proofs explode.

### The pipeline

```
HomogeneousCSP  (Lean; e.g. the corpus CSP php_3_2)
   │
   │  order encoding — VERIFIED IN LEAN (this backend)
   │  integer var x with domain D  ↦  threshold bits  "x ≤ dⱼ"
   ▼
PB constraints over typed threshold variables  (PBVar)
   │
   │  toNat injection  →  PBLean's Sat.PB.Constr   (VERIFIED IN LEAN)
   ▼
OPB file  ──[ RoundingSat, UNTRUSTED ]──▶  VeriPB proof
                                              │
                                              │  [ veripb --elaborate, UNTRUSTED ]
                                              ▼
                                           kernel proof  (committed as a string literal)
   │
   │  PBLean reflection checker  checkProof_sound  (VERIFIED IN LEAN; run by native_decide)
   ▼
formulaUnsat  ──[ verified soundness bridge ]──▶  ¬ csp.isSatisfiable     (kernel-checked theorem)
```

The Lean-side modules implement this in order:

| Module | Role |
|--------|------|
| `PB/CSPSig.lean`, `PB/PBVar.lean` | The encoder's variable signature and typed threshold-variable type (`thr i j` ≡ "integer var `i` is ≤ its `j`-th domain value"). Only valid thresholds exist by typing. |
| `PB/Semantics.lean` | `intValue` (recover the integer from the threshold bits), `monotonicity` (staircase clauses), and the foundational lemma `intValue_mem_values`. |
| `PB/Substitution.lean` | `linear_le_of_threshold_sum` — the single load-bearing arithmetic lemma: a linear constraint over CSP variables becomes a linear PB constraint over threshold bits (gap-weighted coefficients). |
| `PB/SignedPB.lean`, `PB/Encode.lean` | Signed→natural PB normalization and `encodeLinearLe` (+ soundness), the base every linear encoder builds on. |
| `PB/AllDifferent.lean`, `PB/Cardinality.lean`, `PB/LinearNe.lean`, `PB/NotAllEqual.lean`, `PB/BoolGates.lean` | The constraint-family encoders (see "Supported fragment" below), each with a Lean soundness lemma. |
| `PB/ToNat.lean` | Injects typed `PBVar` into `Nat`, maps to PBLean's `Sat.PB.Constr`, and proves `unsat_bridge` (PBLean's `formulaUnsat` ⇒ no typed valuation satisfies all constraints). |
| `PB/Extend.lean` | The generic soundness spine `csp_unsat_generic` (and its aux-free specialization): turns "every CSP solution extends to a PB model" + a PB UNSAT certificate into `¬ ∃ solution`. |
| `PB/Adapter.lean`, `PB/NotAllEqualBridge.lean` | Pattern→fact bridges (`bound_sat`, `linear_le_sat`, `alldifferent_sat`, `at_most_k_sat`, …) and the alternate clean linear-list spine `unsat_of_pb`. |
| `PB/Tactic.lean` | The `csp_reflect_unsat` command (reads a committed kernel proof and discharges `formulaUnsat` via `checkProof_sound` + `native_decide`) and `csp_decide` (shells out to RoundingSat + veripb at elaboration time — non-hermetic, not build-tracked). |

### Trust boundary

**Trusted:**
- Lean's kernel (standard).
- PBLean's PB proof checker. Its soundness (`VeriPB.Reflect.checkProof_sound`) is proved in Lean; it is *run* by `native_decide`, which places the Lean compiler in the trusted base via `Lean.ofReduceBool` — the same trust shape as Lean's `bv_decide` tactic.
- This backend's order-encoder soundness theorems (verified in Lean).

**Untrusted** (a fault is *caught*, never certifies a false theorem):
- RoundingSat (the PB solver) and veripb (the proof elaborator).
- The OPB serializer. If the on-disk OPB or the proof doesn't match the Lean-side PB formula, `checkProof_sound`'s hypothesis fails to discharge and the theorem does not go through.

Every end-to-end theorem has been checked with `#print axioms` to depend on exactly:

```
propext,  Classical.choice,  Quot.sound,
<theorem>_formulaUnsat._native.native_decide.ax_1_1
```

— the three standard Lean/Mathlib axioms plus **one** `native_decide` axiom (the kernel-checked certificate). No `sorryAx`.

### Supported constraint fragment

Linear arithmetic (`≤, ≥, =, <, >`); disequality `≠` (aux-free for var≠const and var≠var; Big-M selector for general linear `≠`); `alldifferent`; cardinality (`at_most_k`, `at_least_k`, `exactly_k`); not-all-equal (binary and multi-valued); and Boolean/circuit gates (AND, OR, NOT, and 2-/3-input XOR — handled as linear or via a circuit identity over `{0,1}`). Non-linear constraints (e.g. `product_eq_var`) are out of scope.

### End-to-end UNSAT theorems

Each row is a kernel-checked `¬ ....isSatisfiable` theorem for a CSP drawn from (or built on) the corpus in `CSP/L2S/Tests/lean/`. All are axiom-clean in the sense above.

| Theorem | Module | Corpus | What it certifies |
|---------|--------|--------|-------------------|
| `php_3_2_unsat` | `Pigeonhole.lean` | `35_pigeonhole` | 3 pigeons cannot injectively occupy 2 holes (`alldifferent`). |
| `php_5_4_unsat` | `Pigeonhole.lean` | `35_pigeonhole` | 5 pigeons cannot injectively occupy 4 holes. |
| `schur_2_5_unsat` | `Schur.lean` | `11_schur` | `{1..5}` has no sum-free 2-colouring (Schur S(2)=4). |
| `schur_3_14_unsat` | `Schur3.lean` | `11_schur` | `{1..14}` has no sum-free 3-colouring (Schur S(3)=13). |
| `vdw_2_3_9_unsat` | `VanDerWaerden.lean` | `33_van_der_waerden` | No 2-colouring of `{1..9}` avoids a monochromatic 3-term AP (W(2,3)=9). |
| `ramsey_3_3_K6_unsat` | `Ramsey.lean` | `34_ramsey` | Every 2-colouring of K₆'s edges has a monochromatic triangle (R(3,3)=6). |
| `k3_2col_unsat` | `GraphColoring.lean` | `02_color` | The triangle K₃ is not 2-colourable. |
| `k4_3col_unsat` | `GraphColoring.lean` | `02_color` | K₄ is not 3-colourable (χ(K₄)=4). |
| `k2_forbidden_unsat` | `ForbiddenColoring.lean` | `02_color` | K₂ with colour 1 forbidden at both endpoints is uncolourable. |
| `nqueens_2_unsat` | `NQueens.lean` | `08_queens` | No 2-queens placement on a 2×2 board. |
| `nqueens_3_unsat` | `NQueens.lean` | `08_queens` | No 3-queens placement on a 3×3 board. |
| `langford_2_2_unsat` | `Langford.lean` | `10_langford_simple` | Langford pairing L(2,2) has no solution. |
| `sudoku_4_contradictory_unsat` | `Sudoku.lean` | `19_sudoku` | A 4×4 Sudoku with two equal row-0 givens is unsolvable. |
| `latin_2_contradictory_unsat` | `Latin.lean` | `07_latin_squares` | A binary-encoded order-2 Latin square with contradictory givens is unsolvable. |
| `full_adder_correct_unsat` | `FullAdder.lean` | `28_full_adder_verification` | A full adder cannot violate `a+b+cin = sum + 2·cout` (correctness). |
| `ripple_carry_4bit_correct_unsat` | `RippleCarry.lean` | `29_ripple_carry_adder` | A 4-bit ripple-carry adder cannot violate its addition spec. |
| `xor_equivalence_unsat` | `CircuitEquiv.lean` | `31_circuit_equivalence` | Two 2-input XOR implementations are equivalent (miter is UNSAT). |
| `circuit_majority3_unsat` | `Circuit.lean` | `32_circuit_at_least` | The 3-input majority (carry) circuit: ≥2 true inputs forces carry = 1. |
| `paley_13_4_unsat` | `Paley.lean` | `36_paley` | α(Paley(13)) ≤ 3 — the Paley graph on 13 vertices has no independent set of size 4. |
| `magic_hexagon_2_unsat` | `MagicHexagon.lean` | (inline model) | No order-2 normal magic hexagon: `1..7` cannot fill the 7 cells with all lines equal (forced line sum `28/3`). |

Three smaller demonstrations of the pipeline (not corpus problems) live in `Demo.lean`, `DemoGeneric.lean`, and `DemoHomogeneous.lean`.

### Build and verify

```bash
lake exe cache get     # pre-built Mathlib oleans (avoids a 30+ min build)
lake build             # compiles EVERYTHING, including every UNSAT theorem above
```

A clean `lake build` **is** the verification: the lakefile uses `globs := #[.andSubmodules `CSP]`, so a bare build compiles the CSP root *and all submodules* — the PB backend, the proofs, and every `_unsat` theorem (kernel proofs are embedded as string literals and re-checked by `native_decide` during the build). A successful build prints `Build completed successfully (8635 jobs)`.

Verifying committed theorems needs **only Lean + the Mathlib cache** — RoundingSat and veripb are *not* required to re-check them, only to generate a certificate for a *new* instance.

```bash
# verify one instance and inspect its trust boundary
lake build CSP.L2S.Backends.PB.Pigeonhole
echo 'import CSP.L2S.Backends.PB.Pigeonhole
#print axioms CSP.L2S.PB.Pigeonhole.php_3_2_unsat' > /tmp/chk.lean
lake env lean /tmp/chk.lean
```

### Adding a new UNSAT instance

The full, self-contained playbook — locate a corpus CSP, build its `CSPSig`, wire corpus membership, reuse an existing encoder, generate the external certificate with RoundingSat + veripb, and confirm the axiom set — is in **[`docs/ADDING_UNSAT_INSTANCES.md`](docs/ADDING_UNSAT_INSTANCES.md)**, with one fully worked example. The implemented-status summary and architecture overview are in **[`PLAN.md`](PLAN.md)**.

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
    ├── Core.lean             # HomogeneousCSP foundations
    ├── Constraints.lean      # 50+ constraint types
    ├── Translate.lean        # Unified translation API
    ├── Backend.lean          # Backend interface + translateWith driver
    ├── Backends/
    │   ├── MiniZinc.lean     # MiniZinc code generation
    │   ├── SMTLIB.lean       # SMT-LIB code generation
    │   └── PB/               # Verified pseudo-Boolean UNSAT backend (above)
    ├── Embedding.lean        # Embedding into the heterogeneous CSP
    ├── Equivalence.lean      # Equivalence theory
    ├── Symmetry.lean         # Symmetry breaking theory
    ├── Proofs/               # Verified theorems (see below)
    └── Tests/lean/           # 36 example problems (also instance generators)
```

## Requirements

| Tool | Purpose | Link |
|------|---------|------|
| **Lean 4 + elan** | Theorem prover (required) | [lean-lang.org/install](https://lean-lang.org/install/) |
| **MiniZinc** | Constraint solver for the translation backend (optional) | [minizinc.org](https://www.minizinc.org/downloads/) |
| **Z3 / CVC5** | SMT solvers for the translation backend (optional) | [z3](https://github.com/Z3Prover/z3/releases) / [cvc5](https://github.com/cvc5/cvc5/releases) |
| **RoundingSat** | PB solver — only to *generate* a new UNSAT certificate (optional) | [gitlab.com/MIAOresearch/software/roundingsat](https://gitlab.com/MIAOresearch/software/roundingsat) |
| **veripb** | PB proof elaborator — only to *generate* a new certificate (optional) | [gitlab.com/MIAOresearch/software/VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) |

The Lean dependency **PBLean** (the `veripb` Lake package providing `VeriPB.Reflect.checkProof_sound`) is fetched automatically by Lake — it is pinned in `lake-manifest.json` and needs no manual install.

Install [elan](https://lean-lang.org/install/manual/) so the correct Lean version (pinned in `lean-toolchain`) is fetched automatically:

```bash
sudo apt install git curl                                      # git + curl
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh         # elan (choose 1 for the default)
source $HOME/.elan/env                                         # add elan to PATH
```

## Building the Project

```bash
# 1. Clone
git clone https://github.com/leansolving/leancsp.git
cd leancsp

# 2. Pre-built Mathlib cache (IMPORTANT: saves 30+ min of compiling Mathlib)
lake exe cache get

# 3. Build everything (root + all submodules: L2S, proofs, PB backend, tests)
lake build
```

A successful build ends with `Build completed successfully (8635 jobs)`. The only warnings are two `String.dropRight` deprecation notices in `Tests/BenchmarkAll.lean` (a benchmark helper); the verified code is warning-free and `sorry`-free.

To re-check a single module once its imports are built: `lake env lean <path/to/File.lean>`.

## Usage

### Modelling CSPs

The L2S framework uses `HomogeneousCSP` — a number of integer variables and a list of constraints:

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

def graph_coloring (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : HomogeneousCSP :=
  let bounds := (List.finRange nodes).map fun v => bound v 1 colors
  let edge_constrs := edges.map fun (u, v) => not_equal u v
  ⟨nodes, bounds ++ edge_constrs⟩
```

Available constraints: `alldifferent`, `count`, `element`, `sum_eq`, `linear_eq`, `less_than`, `not_equal`, `at_most_k`, `at_least_k`, `bound`, and 40+ more (see `L2S/Constraints.lean` and `L2S/README.md`).

> **Bounds are constraints, not domains.** A variable's range comes from a `bound v lb ub` constraint. During translation, `bound` patterns become solver variable declarations; a variable with no `bound` defaults to `[-1000, 1000]`.

### Solver translation (MiniZinc / SMT-LIB)

```lean
import CSP.L2S.Translate

open CSP.L2S

def my_csp : HomogeneousCSP := ...

def main : IO Unit := do
  saveTo my_csp "model.mzn" BackendType.MiniZinc
  saveTo my_csp "model.smt2" BackendType.SMTLIB

-- or, to get the string directly:
#eval translateTo my_csp BackendType.MiniZinc
```

```bash
lake env lean --run MyFile.lean   # runs `main`, emits the files
minizinc model.mzn                # or: z3 model.smt2  /  cvc5 model.smt2
```

### Example: Petersen graph coloring

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
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)   -- spokes
  ]
  let bounds := (List.finRange nodes).map fun v => bound v 1 3
  let edge_constrs := edges.map fun (u, v) => not_equal ⟨u, by omega⟩ ⟨v, by omega⟩
  ⟨nodes, bounds ++ edge_constrs⟩

def main : IO Unit := do
  saveTo petersen "petersen.mzn" BackendType.MiniZinc
```

## Verified Proofs

Beyond the UNSAT certificates, the repository contains verified meta-theorems about CSPs (in `CSP/L2S/Proofs/`).

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
| `CircuitInputSymmetryBreaking.lean` | A permutation of symmetric circuit inputs is a variable symmetry; lex-leader breaks it |
| `CircuitTwinSymmetryBreaking.lean` | A lexicographic ordering on any subset of twin inputs (identical fanout) breaks symmetry equisatisfiably |

## Main Definitions

### CSP Equivalence

Two CSPs are equivalent if there is a bijection between their solution sets:

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
