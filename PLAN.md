# Implementation Plan: Verified UNSAT Certificates for Finite-Domain CSPs in Lean 4

**Project name (working title):** `leancsp-pb` — a verified pseudo-Boolean encoding backend for finite-domain constraint satisfaction problems.

**Status:** Self-contained implementation plan. Reader is assumed to have no prior context on this project; all dependencies, design decisions, and milestones are spelled out below.

**Target audience for the plan:** a Lean 4 developer or AI agent tasked with building this system from scratch.

---

## 1. Project goal

Given a finite-domain constraint satisfaction problem (CSP) defined in Lean 4 using the [leancsp](https://github.com/leansolving/leancsp) library, produce a kernel-checked Lean 4 theorem of the form

```lean
theorem my_csp_unsat : ¬ CSP.is_satisfiable my_csp
```

via an automated pipeline:

```
Lean CSP definition (leancsp HomogeneousCSP)
     │
     ├──[verified order-encoded translation, in Lean]──▶ PB (pseudo-Boolean) constraint database
                                                              │
                                                              ├──[OPB serialization]──▶ .opb file
                                                                                          │
                                                                                          ├──[RoundingSat, external]──▶ VeriPB raw proof
                                                                                                                          │
                                                                                                                          ├──[veripb --elaborate, external]──▶ VeriPB kernel proof
                                                                                                                                                                  │
                                                                                                                                                                  └──[PBLean reflection checker, in Lean]──▶ Lean theorem
```

The SAT/PB solver and the proof elaborator are **untrusted oracles**: only the encoder, the OPB serializer (for the parsing direction), and PBLean's checker need to be verified in Lean. The user invokes a single tactic `csp_decide` and receives a Lean theorem.

### What this project IS

- A verified compiler from leancsp's `HomogeneousCSP n` type to PB constraint sets.
- A composition theorem chaining "CSP solution → PB model" with PBLean's UNSAT checker to derive `¬ csp.is_satisfiable`.
- A `csp_decide` tactic that automates the full pipeline.
- A benchmark suite drawn from leancsp's existing test corpus, demonstrating UNSAT certification across 9 problem families.

### What this project is NOT (paper-1 scope boundary)

- Not an optimization tool (no objective handling). Optimization with certified optimality is a follow-up project.
- Not a complete leancsp-fragment encoder: paper 1 handles linear arithmetic, alldifferent, cardinality, and Boolean primitives. Globals like `element`, `table`, `regular`, `circuit`, `cumulative` are deferred.
- Not a multiplication/non-linear handler.
- Not a competition-grade tool — focus is on verified correctness, not raw solver throughput.

### Why this matters

Existing verified CSP work either targets MiniZinc/SMT (unverified back-end) or formalizes specific problem encodings one at a time. This project provides a **generic verified backend** producing kernel-checked UNSAT theorems. Three concrete payoffs:

1. **Verified-encoding gap closure.** Anyone using leancsp to model a CSP gets verified UNSAT certificates without writing encoding-specific proofs.
2. **Cutting-planes proof power.** PB targets allow short proofs for counting-heavy CSPs (pigeonhole, Hall-set, balanced partitioning) where SAT-based pipelines explode.
3. **Composability.** The output is a Lean theorem, not a verdict — usable as a lemma in downstream formal developments.

---

## 2. Dependencies and external resources

### Lean 4 ecosystem

- **Lean 4**, version pinned via `elan` to match the dependencies (currently `leanprover/lean4:v4.28.0-rc1` for PBLean).
- **Mathlib** — required by leancsp; not required by PBLean. The combined project pulls in Mathlib via leancsp.
- **`lake`** — Lean's build tool.
- Install: `curl https://elan.lean-lang.org/elan-init.sh -sSf | sh`.

### Lean libraries (Lake dependencies)

#### leancsp

- **URL:** <https://github.com/leansolving/leancsp>
- **Purpose:** the front end — defines `HomogeneousCSP n`, `ConstraintPattern n`, `is_solution`, `is_satisfiable`. Already has unverified MiniZinc and SMT-LIB backends; we add a verified PB backend.
- **Key files to read first:** `CSP/Core.lean` (the abstract `CSP` type), `CSP/L2S/Core.lean` (the `HomogeneousCSP` specialization), `CSP/L2S/Constraints.lean` (the constraint DSL with 50+ patterns), `CSP/L2S/Tests/lean/` (the 32 example problems).
- **Add to `lakefile.lean`:**

```lean
require leancsp from git "https://github.com/leansolving/leancsp" @ "main"
```

#### PBLean

- **URL:** <https://github.com/leansolving/pblean>
- **Paper:** S. Szeider, *PBLean: Pseudo-Boolean Proof Certificates for Lean 4*, PoS 2026, arXiv:2602.08692
- **Purpose:** the back end — imports VeriPB proof certificates into Lean via reflection (`native_decide`). Provides `PBConstr`, `OPBFormula`, the reflection checker `checkProofBool`, and the soundness theorem `checkProofBool_sound`.
- **Key files to read first:** `VeriPB/Tactic/Sat/PseudoBoolean.lean` (~880 LoC kernel — PB constraint types and 15 soundness lemmas), `VeriPB/Tactic/Sat/Reflect.lean` (~2500 LoC reflection checker), `VeriPB/Tactic/Sat/IndependentSet.lean` (example of the encode + soundness + bridge pattern, applied to Paley independent sets).
- **Add to `lakefile.lean`:**

```lean
require pblean from git "https://github.com/leansolving/pblean" @ "main"
```

#### Std.Sat (Lean core)

PBLean's CNF types build on `Std.Sat.CNF`. We don't import Std.Sat directly but it's available transitively.

### External binaries

#### RoundingSat

- **URL:** <https://gitlab.com/MIAOresearch/software/roundingsat>
- **Purpose:** the PB solver producing native cutting-planes proof logs. Used here in decision mode (UNSAT certificate generation).
- **Install:**
  ```
  git clone https://gitlab.com/MIAOresearch/software/roundingsat.git
  cd roundingsat && make
  ```
- **Invocation (for UNSAT certificate generation):**
  ```
  roundingsat --proof-log=problem.proof problem.opb
  ```
  Produces `problem.proof` in raw VeriPB format.

#### VeriPB (proof elaboration)

- **URL:** <https://gitlab.com/MIAOresearch/software/VeriPB>
- **Purpose:** elaborates raw VeriPB proofs (compact, solver-emitted) into kernel format (fully explicit) consumable by PBLean.
- **Install:** Python package, follow the repo's README.
- **Invocation:**
  ```
  veripb --elaborate problem.opb problem.proof problem.kernel.pbp
  ```

### Existing related projects (reference, not dependencies)

#### LeanSMS

- **URL:** <https://github.com/leansolving/leansms>
- **Purpose:** verified pipeline for graph non-existence theorems via SMS + SAT + LRAT. Architecturally analogous to this project but uses LRAT (CNF) instead of VeriPB (PB).
- **Use as reference:** the pattern of `encode + soundness + bridge`, the use of `Std.Sat.CNF`, the verified `SequentialCounter.lean` (Sinz at-most-k) which is the canonical example of a verified cardinality encoder.

#### `~/work/reconstruct` (local)

Stefan's CSP-to-CNF reconstruction project; contains a Sugar/BEE/PicatSAT runner and benchmark instances. Useful as differential-testing baselines but not a dependency.

---

## 3. High-level architecture

### Trust model

Three layers are trusted:

1. **Lean's kernel** (standard assumption).
2. **PBLean's reflection checker.** Its soundness is proved in Lean; applying it via `native_decide` places the Lean compiler in the TCB through `Lean.ofReduceBool`. Same trust shape as Lean's `bv_decide` tactic.
3. **The encoder's soundness theorems** (this project — verified in Lean).

Untrusted:
- The PB solver (RoundingSat).
- The proof elaborator (veripb).
- The .opb file on disk — if it doesn't match the Lean-side PB formula, PBLean's check fails on the parse step or the bridge theorem fails.

### File layout

The project is organized as a new Lake package depending on leancsp and PBLean:

```
leancsp-pb/                               # the new project
├── lakefile.lean                         # Lake config: deps on leancsp, PBLean
├── lean-toolchain                        # pins Lean version
├── README.md
├── LeancspPB.lean                        # umbrella import
└── LeancspPB/
    ├── Core/
    │   ├── CSPSig.lean                   # CSPSig structure
    │   ├── PBVar.lean                    # PBVar inductive type + DecidableEq
    │   ├── LitConst.lean                 # LitConst + mkLeLit smart constructor
    │   └── Semantics.lean                # intValue, monotonicity, orderConsistent
    ├── SignedPB/
    │   ├── Basic.lean                    # SignedPBConstr type + sat
    │   └── Normalize.lean                # signed → natural PBConstr + soundness
    ├── Substitution.lean                 # the key theorem linear_le_of_threshold_sum
    ├── Encode/
    │   ├── Monotonicity.lean             # staircase clauses
    │   ├── Linear.lean                   # Σ aᵢxᵢ ≤ b encoding
    │   ├── Derived.lean                  # =, ≥, <, > from ≤
    │   ├── Disequality.lean              # ≠ via selector
    │   ├── AllDifferent.lean             # per-value cardinality decomposition
    │   ├── Cardinality.lean              # at_most_k, at_least_k, exactly_k
    │   ├── Boolean.lean                  # ∧, ∨, ¬, ↔, → via Tseitin
    │   └── Reification.lean              # Big-M reification helpers, fresh aux state
    ├── ToOPB.lean                        # PBVar → Nat injection, OPB serialization, toOPB_unsat
    ├── Bridge/
    │   ├── Fragment.lean                 # inPBFragment predicate over ConstraintPattern
    │   ├── SatEncodingData.lean          # extracting bounds from HomogeneousCSP
    │   ├── EncodingResult.lean           # the EncodingResult structure
    │   └── Theorem.lean                  # csp_unsat_of_veripb top-level theorem
    ├── Tactic/
    │   └── CspDecide.lean                # the csp_decide tactic
    └── Tests/
        ├── Demo.lean                     # toy UNSAT example
        ├── NQueensForbidden.lean         # N-Queens with forbidden cells
        ├── QWH.lean                      # quasigroup-with-holes
        ├── Sudoku.lean                   # hard UNSAT Sudoku
        ├── GraphColoring.lean            # pre-colored graph k-coloring
        ├── Langford.lean                 # Langford pairing
        ├── Schur.lean                    # Schur triples
        ├── Golomb.lean                   # Golomb ruler infeasibility
        ├── AllInterval.lean              # all-interval series
        └── Costas.lean                   # Costas arrays
```

---

## 4. Core Lean types

### 4.1 `CSPSig` — the encoder's variable signature

A CSP has a fixed set of integer variables (with per-variable finite domains), Boolean variables, and auxiliary variables (used for Tseitin encoding and reification). Domains are arbitrary finite subsets of `ℤ`, represented as sorted lists.

```lean
import Mathlib.Data.List.Sort

namespace LeancspPB

/-- Signature of a PB encoding: variable counts and per-variable domains. -/
structure CSPSig where
  nInt   : Nat
  nBool  : Nat
  nAux   : Nat
  values : Fin nInt → List Int
  sorted : ∀ i, (values i).Sorted (· < ·)
  nonempty : ∀ i, (values i).length > 0

namespace CSPSig

/-- Number of threshold variables for integer variable i.
    Equals |domain| − 1 (the "x ≤ max" threshold is always true and is not represented). -/
def width (S : CSPSig) (i : Fin S.nInt) : Nat := (S.values i).length - 1

/-- The j-th domain value for variable i. -/
def valueAt (S : CSPSig) (i : Fin S.nInt) (j : Fin (S.values i).length) : Int :=
  (S.values i).get j

/-- Maximum of variable i's domain. -/
def maxVal (S : CSPSig) (i : Fin S.nInt) : Int :=
  (S.values i).getLast (List.length_pos.mp (S.nonempty i))

/-- The j-th gap between adjacent domain values: values_i[j+1] − values_i[j]. -/
def gap (S : CSPSig) (i : Fin S.nInt) (j : Fin (S.width i)) : Int := by
  -- values i has length ≥ 2 if width > 0; gap is positive by sorted
  exact (S.values i).get ⟨j.val + 1, by
    have : j.val < S.width i := j.isLt
    simp [width] at this
    omega⟩ - (S.values i).get ⟨j.val, by
    have : j.val < S.width i := j.isLt
    simp [width] at this
    omega⟩

end CSPSig
```

### 4.2 `PBVar` — the propositional variable type

Three constructors: original Boolean CSP variables, threshold variables for integer variables, and auxiliary variables. **The type is finite** (no `Nat` constructors) so OPB serialization sees a closed variable count.

```lean
/-- Propositional variables used in the PB encoding. -/
inductive PBVar (S : CSPSig) where
  | bool : Fin S.nBool → PBVar S
  | thr  : (i : Fin S.nInt) → Fin (S.width i) → PBVar S
  | aux  : Fin S.nAux → PBVar S
  deriving DecidableEq, Repr, Hashable
```

`thr i j` means "integer variable `i` is at most `valueAt(i, j)`". Crucially, only valid thresholds exist by the type system.

### 4.3 `LitConst` and `mkLeLit` — smart literal construction

Paper-level "x ≤ k" thresholds may fall outside the domain (e.g., k below the smallest value or k at/above the largest). These don't have corresponding `thr` variables; they collapse to constants.

```lean
inductive LitConst (V : Type) where
  | lit   : Std.Sat.Literal V → LitConst V
  | const : Bool → LitConst V
  deriving Repr

namespace LitConst

/-- For "x ≤ k" with variable i and threshold k:
    - if k < min(D_i): always false (no valid threshold).
    - if k ≥ max(D_i): always true.
    - otherwise: return the threshold variable for the largest domain value ≤ k. -/
def mkLeLit (S : CSPSig) (i : Fin S.nInt) (k : Int) : LitConst (PBVar S) :=
  let vs := S.values i
  -- Find the largest j such that vs.get j ≤ k.
  match vs.findIdx? (· > k) with
  | none =>
      .const true        -- no value > k, so x ≤ k always (x ≤ max(D) ≤ k)
  | some 0 =>
      .const false       -- first value > k, so x > k always
  | some (j + 1) =>
      -- Want threshold at index j (largest ≤ k).
      -- Must check j < width = vs.length - 1.
      if h : j < S.width i then
        .lit (.pos (.thr i ⟨j, h⟩))
      else
        .const true       -- j = vs.length - 1; "x ≤ vs[last]" is max(D), always true
end LitConst
```

Correctness: `mkLeLit S i k` evaluates to `xᵢ ≤ k` under any order-consistent valuation. State and prove `mkLeLit_correct`.

### 4.4 `Valuation` and `intValue` — semantics

```lean
abbrev Valuation (S : CSPSig) := PBVar S → Bool

namespace Valuation

/-- Integer value of variable i under valuation v.
    Defined as: max of domain minus the gap-weighted sum of true thresholds. -/
def intValue (S : CSPSig) (v : Valuation S) (i : Fin S.nInt) : Int :=
  S.maxVal i - (∑ j : Fin (S.width i), S.gap i j * (v (.thr S i j)).toInt)

end Valuation

/-- Monotonicity constraints: for each integer variable i and each adjacent
    threshold pair (j, j+1) with j + 1 < width i:
       t_{i,j+1} ≥ t_{i,j}     i.e.     1·t_{i,j+1} + 1·¬t_{i,j} ≥ 1. -/
def CSPSig.monotonicity (S : CSPSig) : List (PBConstr (PBVar S)) :=
  -- Iterate over adjacent pairs (j, j+1) via List.zip, avoiding Fin (width - 1) arithmetic.
  sorry  -- (implementation: build the staircase clauses)

def Valuation.orderConsistent {S : CSPSig} (v : Valuation S) : Prop :=
  ∀ c ∈ S.monotonicity, PBConstr.sat v c
```

**Key lemma to prove early:**

```lean
theorem Valuation.intValue_mem_values
    (S : CSPSig) (v : Valuation S) (hv : v.orderConsistent) (i : Fin S.nInt) :
    v.intValue i ∈ (S.values i)
```

This says: under monotonicity, the recovered integer value is always one of the declared domain values. Proof: induction on the number of true thresholds, using monotonicity.

---

## 5. The substitution theorem (technical core)

This is the single load-bearing arithmetic lemma. Under monotonicity, a linear arithmetic constraint over CSP variables converts to a linear PB constraint over threshold variables, with coefficients incorporating the domain gaps.

```lean
/-- Under monotonicity, the linear sum Σ aᵢ xᵢ ≤ b corresponds to a single
    linear constraint over the threshold variables, with gap-weighted coefficients. -/
theorem linear_le_of_threshold_sum
    (S : CSPSig) (v : Valuation S) (hv : v.orderConsistent)
    (terms : List (Int × Fin S.nInt)) (b : Int) :
    (∑ p ∈ terms, p.1 * v.intValue p.2) ≤ b
      ↔
    (∑ p ∈ terms, p.1 *
      (∑ j : Fin (S.width p.2), S.gap p.2 j * (v (.thr S p.2 j)).toInt))
      ≥ (∑ p ∈ terms, p.1 * S.maxVal p.2) - b
```

**Proof sketch.** By definition of `intValue`, each `v.intValue i = maxVal i − Σ_j gap·t`. Distribute the outer sum, collect maxVal terms on one side, threshold-sum terms on the other, flip the inequality direction. ~30 lines.

**Why this theorem is the technical core:**

- Every linear-arithmetic encoding (`≤`, `≥`, `=`, `<`, `>`) reduces to this lemma.
- All encodings producing PB constraints from CSP constraints are eventually justified through it.
- The lemma generalizes the interval-domain case (gaps all 1, `maxVal = hi`, `width = hi - lo`) used in the order-encoding literature (Crawford-Baker, Tamura, Abío et al.). The gap-coefficient generalization is what enables arbitrary finite domains.

---

## 6. Per-constraint encodings

The encoder is a function `ConstraintPattern n → List (SignedPBConstr (PBVar S))`, with each constraint family handled by its own module.

### 6.1 Signed-PB intermediate form

PBLean's kernel uses non-negative coefficients and degree. Our encoders naturally produce signed coefficients. Bridge via a normalization layer.

```lean
namespace LeancspPB

/-- Encoder-level PB constraint with signed coefficients (intermediate form).
    Semantics: Σ (a, ℓ) ∈ terms, a · ⟦ℓ⟧ ≥ rhs. -/
structure SignedPBConstr (V : Type) where
  terms : List (Int × Std.Sat.Literal V)
  rhs   : Int
  deriving Repr

namespace SignedPBConstr

def sat (v : V → Bool) (c : SignedPBConstr V) : Prop :=
  (c.terms.foldl (init := 0) fun acc (a, ℓ) => acc + a * (Literal.eval v ℓ).toInt) ≥ c.rhs

end SignedPBConstr

/-- Normalize to PBLean's natural-coefficient form.
    Rules:
    - Zero coefficients dropped.
    - Negative coefficients: a · ℓ → |a| · ¬ℓ, shift degree by |a|.
    - Tautological constraint (rhs ≤ 0 after normalization): return None (no PB constraint emitted).
    - Immediate contradiction (rhs > sum of coefficients): return Some(empty), which forces UNSAT. -/
def normalize {V : Type} [DecidableEq V] (c : SignedPBConstr V) : Option (PBConstr V) :=
  sorry

theorem normalize_sat_iff
    {V : Type} [DecidableEq V] (c : SignedPBConstr V) (c' : PBConstr V)
    (h : normalize c = some c') :
    ∀ v, c.sat v ↔ PBConstr.sat v c'

theorem normalize_none_iff_tautology
    {V : Type} [DecidableEq V] (c : SignedPBConstr V) (h : normalize c = none) :
    ∀ v, c.sat v
```

### 6.2 Linear `≤`

For `Σ aᵢ xᵢ ≤ b` with all `aᵢ ≠ 0`:

```lean
def encodeLinearLe (S : CSPSig) (terms : List (Int × Fin S.nInt)) (b : Int) :
    SignedPBConstr (PBVar S) :=
  -- Build the constraint Σᵢ aᵢ · Σⱼ gap_{i,j} · t_{i,j} ≥ (Σᵢ aᵢ · maxVal i) − b.
  let pb_terms : List (Int × Std.Sat.Literal (PBVar S)) :=
    terms.flatMap fun (a, i) =>
      (List.finRange (S.width i)).map fun j =>
        (a * S.gap i j, .pos (.thr i j))
  let rhs := (terms.foldl (init := 0) fun acc (a, i) => acc + a * S.maxVal i) - b
  { terms := pb_terms, rhs := rhs }

theorem encodeLinearLe_sound
    (S : CSPSig) (v : Valuation S) (hv : v.orderConsistent)
    (terms : List (Int × Fin S.nInt)) (b : Int)
    (h : (∑ p ∈ terms, p.1 * v.intValue p.2) ≤ b) :
    (encodeLinearLe S terms b).sat v
```

Proof: directly from `linear_le_of_threshold_sum`.

### 6.3 Derived `=, ≥, <, >`

- `=`: emit both `≤` and `≥`.
- `≥`: emit `Σ −aᵢ xᵢ ≤ −b`.
- `<`: emit `Σ aᵢ xᵢ ≤ b − 1`.
- `>`: emit `Σ −aᵢ xᵢ ≤ −b − 1`.

Each is a 5-line wrapper around `encodeLinearLe`.

### 6.4 `≠` via selector encoding

For `Σ aᵢ xᵢ ≠ b`, allocate one fresh `s : PBVar.aux _` and emit two implications:

```
s  ⇒ Σ aᵢ xᵢ ≤ b − 1     (Big-M form)
¬s ⇒ Σ aᵢ xᵢ ≥ b + 1
```

The Big-M is `M = Σᵢ |aᵢ| · (maxVal i − minVal i) + 1`, the maximum range of the linear sum over domain bounds.

```lean
def encodeNe (S : CSPSig)
    (freshAux : Nat → Fin S.nAux)
    (terms : List (Int × Fin S.nInt)) (b : Int) :
    List (SignedPBConstr (PBVar S)) × Nat :=
  -- Returns (constraints, next-fresh-aux-index).
  sorry
```

Special cases that simplify:
- `xⱼ ≠ v` (single variable, single value): single PB clause `t_{j, j_v−1} + ¬t_{j, j_v} ≥ 1` (with the out-of-range conventions handled by `mkLeLit`).
- `xᵢ ≠ xⱼ` (two variables): per-value indicator `[xᵢ=v] + [xⱼ=v] ≤ 1` for each `v ∈ values_i ∩ values_j`.

### 6.5 `alldifferent`

For variables `x_1, …, x_n` with arbitrary finite domains:

```
∀ v ∈ ⋃ᵢ values_i :  Σⱼ [xⱼ = v] ≤ 1
```

where `[xⱼ = v]` is:
- `0` if `v ∉ values_j` (omitted from the sum),
- `t_{j, j_v} − t_{j, j_v − 1}` otherwise (with `t_{j, -1} = 0` and `t_{j, last} = 1` handled by `mkLeLit`).

```lean
def encodeAllDifferent (S : CSPSig) (vars : List (Fin S.nInt)) :
    List (SignedPBConstr (PBVar S)) :=
  let allValues : List Int :=
    (vars.flatMap fun i => S.values i).dedup.mergeSort (· < ·)
  allValues.map fun v =>
    let pb_terms : List (Int × Std.Sat.Literal (PBVar S)) :=
      vars.filterMap fun i =>
        if v ∈ S.values i then
          -- [xᵢ = v] = t_{i, j_v} - t_{i, j_v - 1}
          some sorry  -- (the indicator difference)
        else none
    { terms := pb_terms, rhs := -1 }  -- meaning Σ [xⱼ = v] ≤ 1 in our ≥ form is -Σ ≥ -1
```

### 6.6 Cardinality

Native PB constraints — no encoding overhead.

```lean
def encodeAtMostK (S : CSPSig) (vars : List (Fin S.nBool)) (k : Nat) :
    SignedPBConstr (PBVar S) :=
  -- Σ ¬bᵢ ≥ n − k  is equivalent to Σ bᵢ ≤ k.
  let terms := vars.map fun i => (1, .neg (.bool i))
  { terms := terms, rhs := vars.length - k }

def encodeAtLeastK (S : CSPSig) (vars : List (Fin S.nBool)) (k : Nat) :
    SignedPBConstr (PBVar S) :=
  let terms := vars.map fun i => (1, .pos (.bool i))
  { terms := terms, rhs := k }

def encodeExactlyK (S : CSPSig) (vars : List (Fin S.nBool)) (k : Nat) :
    List (SignedPBConstr (PBVar S)) :=
  [encodeAtMostK S vars k, encodeAtLeastK S vars k]
```

### 6.7 Boolean primitives (Tseitin)

Standard PB-form clauses for `∧, ∨, ¬, ↔, →`. Each connective emits 2–3 PB constraints. Use a Tseitin translator with state monad for fresh auxiliaries.

```lean
inductive BoolExpr (S : CSPSig) where
  | var  : Fin S.nBool → BoolExpr S
  | const : Bool → BoolExpr S
  | not  : BoolExpr S → BoolExpr S
  | and  : BoolExpr S → BoolExpr S → BoolExpr S
  | or   : BoolExpr S → BoolExpr S → BoolExpr S
  | iff  : BoolExpr S → BoolExpr S → BoolExpr S

def tseitin (S : CSPSig) (e : BoolExpr S) :
    StateM Nat (Std.Sat.Literal (PBVar S) × List (SignedPBConstr (PBVar S))) :=
  sorry
```

### 6.8 Not-all-equal / forbidden monochromatic tuple (`schur_triple` and its k-ary generalization)

**Empirically surfaced** by encoding the PBLean showcase problems as CSPs (`Tests/lean/{11_schur,33_van_der_waerden,34_ramsey}.lean`): three of the six showcase UNSAT families (Schur, Van der Waerden, Ramsey R(3,3)) reduce to a single pattern — `schur_triple v₁ v₂ v₃`, i.e. *the three variables are not all equal* — which has **no subsection in §6 and no line in the M4 milestone**. It is the highest-frequency PB-encoding gap the corpus reveals, so it belongs ahead of the §6.4/§6.6 items in priority.

It is **not a monolithic primitive**; the encoding splits on domain width:

- **Boolean domains** (`{0,1}` — vdW, Ramsey edge colours): not-all-equal over `b₁…bₘ` is exactly two cardinality constraints — `Σ bᵢ ≥ 1` (not all false) **and** `Σ ¬bᵢ ≥ 1` (not all true). So once §6.6 lands, the binary case is free; the encoder just dispatches to `encodeAtLeastK` twice.
- **Multi-valued domains** (`{1..k}`, k>2 — Schur 3-colouring, and the same machinery equitable colouring needs): not-all-equal = `(x_a ≠ x_b) ∨ (x_b ≠ x_c)`, a **disjunction of disequalities**. This needs a *reified* version of the §6.4 `≠` selector (a fresh Boolean witnessing each `≠`, combinable in a clause) — strictly more than the hard `≠` of §6.4. **This reified (dis)equality of order-encoded variables is the one genuinely new piece** the showcase set demands.

```lean
-- Binary case: reuse cardinality (§6.6).
def encodeNotAllEqualBool (S : CSPSig) (vars : List (Fin S.nBool)) :
    List (SignedPBConstr (PBVar S)) :=
  [encodeAtLeastK S vars 1,                 -- not all false
   encodeAtMostK  S vars (vars.length - 1)] -- not all true

-- Multi-valued case: needs reified ≠ (extends §6.4), then OR the selectors.
def encodeNotAllEqual (S : CSPSig) (vars : List (Fin S.nInt)) :
    StateM Nat (List (SignedPBConstr (PBVar S))) :=
  sorry  -- fresh sᵢ ↔ (xᵢ ≠ xᵢ₊₁) via reified order-encoding; emit clause Σ sᵢ ≥ 1
```

The k-ary not-all-equal (vdW W(2,4) 4-APs, Ramsey R(3,4) cliques) is the same with a longer scope; the two remaining showcase gaps that are *not* not-all-equal are **count-in-range / global cardinality** (equitable-colouring balance — the catalog's `count` is exact-only) and **conditional/bin-load sums** (bin packing over an assignment variable — needs a global or a one-hot reformulation).

---

## 7. The soundness theorem and bridge to PBLean

The user-facing theorem composes "CSP solution → PB model" with PBLean's UNSAT certificate to derive `¬ is_satisfiable`.

```lean
/-- Data extracted from a HomogeneousCSP that the encoder consumes. -/
structure SatEncodingData (csp : HomogeneousCSP n) where
  values     : Fin n → List Int
  sorted     : ∀ i, (values i).Sorted (· < ·)
  domain_eq  : ∀ i, csp.domain i = (values i).toFinset.toSet
  nonempty   : ∀ i, (values i).length > 0
  fragment   : ∀ c ∈ csp.constraints, c.pattern.inPBFragment

/-- The encoder's full output, bundling everything needed for the bridge theorem. -/
structure EncodingResult (csp : HomogeneousCSP n) (D : SatEncodingData csp) where
  sig     : CSPSig
  origInt : Fin n → Fin sig.nInt
  signed  : List (SignedPBConstr (PBVar sig))           -- pre-normalization
  pb      : List (PBConstr (PBVar sig))                 -- post-normalization
  toOPB   : OPBFormula                                  -- DIMACS-shaped serialization

  extend  : (a : HomogeneousAssignment n) →
            (∀ i, a i ∈ csp.domain i) → Valuation sig

  /-- Original variable values are preserved when input respects the declared domains. -/
  extend_intValue :
    ∀ a (hdom : ∀ i, a i ∈ csp.domain i) i,
      (extend a hdom).intValue (origInt i) = a i

  /-- CSP solution ⇒ PB model. -/
  csp_solution_extends_to_pb_model :
    ∀ a (hsol : csp.is_solution a),
      ∃ hdom : ∀ i, a i ∈ csp.domain i,
        ∀ c ∈ pb, PBConstr.sat (extend a hdom) c

  /-- OPB serialization preserves UNSAT. -/
  toOPB_unsat :
    OPBFormula.Unsat toOPB → PBSet.Unsat pb

/-- The top-level user-facing theorem. -/
theorem csp_unsat_of_veripb
    (csp : HomogeneousCSP n) (D : SatEncodingData csp)
    (E : EncodingResult csp D)
    (proof : VeriPBKernelProof)
    (hcheck : PBLean.Reflect.checkProofBool E.toOPB proof = true) :
    ¬ csp.is_satisfiable := by
  have hOPB : OPBFormula.Unsat E.toOPB :=
    PBLean.Reflect.checkProofBool_sound _ _ hcheck
  have hPB  : PBSet.Unsat E.pb := E.toOPB_unsat hOPB
  intro ⟨a, ha⟩
  obtain ⟨hdom, hmodel⟩ := E.csp_solution_extends_to_pb_model a ha
  exact hPB (E.extend a hdom) hmodel
```

Note: `extend_intValue` requires `a i ∈ csp.domain i` because `intValue` is always in the declared domain; the unconditional version is false for out-of-domain assignments.

---

## 8. OPB serialization

PBLean's checker parses `.opb` files. The serializer must produce a file whose parsed form matches the Lean-side `pb` formula.

```lean
/-- Inject PBVar into Nat with a flat layout: [Boolean vars | thresholds by (i, j) | aux]. -/
def PBVar.toNat (S : CSPSig) : PBVar S → Nat
  | .bool i        => i.val
  | .thr  i j      => S.nBool + offsetThr S i + j.val
  | .aux  k        => S.nBool + totalThr S + k.val
  where
    offsetThr (S : CSPSig) (i : Fin S.nInt) : Nat := …  -- cumulative widths up to i
    totalThr  (S : CSPSig) : Nat := …                   -- Σᵢ width i

theorem PBVar.toNat_injective (S : CSPSig) : Function.Injective (PBVar.toNat S)

/-- Lift a PBConstr (PBVar S) to a PBConstr Nat via toNat. -/
def PBConstr.toNatConstr (S : CSPSig) : PBConstr (PBVar S) → PBConstr Nat :=
  sorry

/-- The OPB formula for the encoding. -/
def CSPSig.toOPB (S : CSPSig) (constraints : List (PBConstr (PBVar S))) : OPBFormula :=
  { vars := S.nBool + totalThr S + S.nAux
    constraints := constraints.map (PBConstr.toNatConstr S) }

theorem CSPSig.toOPB_unsat
    (S : CSPSig) (constraints : List (PBConstr (PBVar S))) :
    OPBFormula.Unsat (CSPSig.toOPB S constraints) → PBSet.Unsat constraints
```

Plus an IO routine `serializeOPB : OPBFormula → IO Unit` for writing the file. The IO routine is **not** part of the trusted base — if it produces an incorrect file, PBLean's parse-and-check step fails, and the bridge theorem doesn't apply.

---

## 9. The `csp_decide` tactic

This is a Lean 4 elaborator that orchestrates the full pipeline.

```lean
namespace LeancspPB.Tactic

open Lean Elab Tactic

/-- The csp_decide tactic.
    Usage: prove a goal `¬ CSP.is_satisfiable my_csp` automatically. -/
elab "csp_decide" csp:term : tactic => do
  -- 1. Elaborate `csp` to a HomogeneousCSP n term.
  -- 2. Extract SatEncodingData (decidable bound extraction from csp.domain).
  -- 3. Call the encoder; obtain EncodingResult.
  -- 4. Serialize to .opb in a temp directory.
  -- 5. Shell out: roundingsat --proof-log=... .opb
  -- 6. Shell out: veripb --elaborate ...
  -- 7. Read the kernel proof back; expose as a term.
  -- 8. Apply csp_unsat_of_veripb with native_decide discharging the checkProofBool = true goal.
  sorry

end LeancspPB.Tactic
```

Implementation reference: PBLean's `independent_set_decide` does most of this for the Paley graph application. Adapt it.

For reproducibility (CI doesn't re-run RoundingSat), also provide:

```lean
elab "csp_decide_from_files" csp:term opbPath:str proofPath:str : tactic => …
```

which takes pre-generated paths to .opb and .pbp files.

---

## 10. Test corpus and benchmark families

leancsp's `CSP/L2S/Tests/lean/` contains 32 example problems. The following 9 produce natural UNSAT-variant benchmark families directly in-fragment.

### 10.1 N-Queens with forbidden cells (`08_queens.lean`)

- **leancsp template:** `Fin n → Fin n` (queen i in column queens(i)) with alldifferent on columns and on diagonals.
- **UNSAT variant:** add `ne_const(queens(r), c)` for each forbidden cell (r, c).
- **Parameterization:** board size N + forbidden-cell pattern. Pick small adversarial patterns making it UNSAT.

### 10.2 QWH — Quasigroup with Holes (`07_latin_squares.lean`)

- **leancsp template:** Latin square of order n: `Fin n × Fin n → Fin n`, alldifferent per row and column.
- **UNSAT variant:** fix k cells via `eq_const`; classical CSP benchmark family.
- **Parameterization:** n + hole count + hole pattern. Standard generator: start with a complete Latin square, remove cells uniformly, add adversarial fixings.

### 10.3 Hard UNSAT Sudoku (`19_sudoku.lean`)

- **leancsp template:** 9×9 grid with alldifferent on rows, columns, and 3×3 boxes.
- **UNSAT variant:** clue patterns from the Sudoku-research literature with no completion.
- **Parameterization:** clue count + specific instances from existing UNSAT-Sudoku catalogs.

### 10.4 Pre-colored graph k-coloring (`02_color.lean`, `12_graph.lean`)

- **leancsp template:** vertex coloring problem.
- **UNSAT variant:** `eq_const` to pre-color a subset V' ⊆ V.
- **Parameterization:** graph + pre-coloring of V'. Pick small (G, V') pairs creating UNSAT.

### 10.5 Langford pairing (`10_langford_simple.lean`)

- **leancsp template:** sequence of length 2n, each number 1..n appears twice with k positions between them.
- **UNSAT variant:** Langford(n) is UNSAT for `n ≡ 2, 3 (mod 4)` (number-theoretic).
- **Parameterization:** n. PBLean already has Langford(6) and Langford(9) UNSAT theorems.

### 10.6 Schur triples (`11_schur.lean`)

- **leancsp template:** partition {1..n} into k sum-free sets.
- **UNSAT variant:** UNSAT for `n > S(k)`. S(2) = 4 so {1..5} is 2-Schur UNSAT; S(3) = 13.
- **Parameterization:** k + n. PBLean already does S(3) = 13.

### 10.7 Golomb ruler (`15_golomb.lean`)

- **leancsp template:** ruler of order n with all pairwise differences distinct.
- **UNSAT variant:** "exists ruler of order n with length ≤ L?" UNSAT for `L < OGR(n)`.
- **Parameterization:** n + L. Try n = 5..8 with various L.

### 10.8 All-interval series (`17_all_interval.lean`)

- **leancsp template:** sequence of length n with all-different elements and all-different consecutive differences.
- **UNSAT variant:** known UNSAT for specific n.
- **Parameterization:** n.

### 10.9 Costas arrays (`18_costas.lean`)

- **leancsp template:** Costas array of order n.
- **UNSAT variant:** Costas arrays don't exist for n=32, n=33 (famously). Smaller n where they do exist may have UNSAT variants under extra constraints.
- **Parameterization:** n.

### Cross-validation against PBLean

PBLean already has verified theorems for Schur S(3) = 13, Langford 6/9, R(3,4) ≤ 9, W(2,4) = 35. Running our generic pipeline against these and checking we reach the same scale validates that the generic encoder matches the per-problem encoders.

### Benchmark metrics

For each instance:
- Lean encoding time
- OPB file size
- RoundingSat solve time
- VeriPB elaboration time
- VeriPB kernel proof size
- PBLean reflection check time
- Total wall-clock

---

## 11. Implementation milestones

### M0: Project setup (1 week)

- Initialize Lake package `leancsp-pb`.
- Add Lake dependencies on `leancsp` and `pblean` (both git refs).
- Pin Lean version matching PBLean.
- Install RoundingSat and VeriPB locally.
- Run PBLean's existing benchmarks end-to-end; confirm the local pipeline (RoundingSat → veripb-elaborate → PBLean reflection check) works.

**Deliverable:** `lake build` succeeds; PBLean's `paley13_alpha` theorem checks locally.

### M1: Core types (1 week)

- Implement `CSPSig` with `nInt`, `nBool`, `nAux`, `values`, helper functions (`width`, `valueAt`, `maxVal`, `gap`).
- Implement `PBVar S` with `DecidableEq, Repr, Hashable`.
- Implement `LitConst` and `mkLeLit` with the smart-constructor logic.
- Implement `Valuation`, `intValue`, `monotonicity`, `orderConsistent`.
- Prove `Valuation.intValue_mem_values`.

**Deliverable:** core types compile; `intValue` correctness lemma proven.

### M2: The substitution theorem (1 week)

- Prove `linear_le_of_threshold_sum` (the single key arithmetic lemma).
- Test on a tiny by-hand example: 2 variables, both in {0, 2, 4}, constraint `x + y ≤ 4`.

**Deliverable:** the technical core theorem proven and tested.

### M3: Linear encoding + smallest end-to-end demo (2 weeks)

- Implement `SignedPBConstr` and `normalize` with `normalize_sat_iff`.
- Implement `encodeLinearLe` with soundness lemma.
- Implement `ToOPB.lean`: variable numbering, OPB serialization, `toOPB_unsat`.
- Implement minimal `EncodingResult`-shaped structure for a hardcoded 3-variable demo.
- Implement minimal `csp_decide`-style tactic that handles the hardcoded demo.
- End-to-end test: prove `¬ ∃ x y z : Fin 4, x.val + y.val + z.val ≤ 2 ∧ x.val + y.val + z.val ≥ 5` via the full pipeline (encode → emit OPB → run RoundingSat → run veripb-elaborate → check via PBLean → close goal).

**Deliverable:** the world's smallest verified-CSP-UNSAT pipeline runs end-to-end.

### M4: Remaining encodings (3 weeks)

- Derived comparisons (`=`, `≥`, `<`, `>`).
- `≠` via selector encoding with Big-M.
- `alldifferent` via per-value cardinality.
- Cardinality (`at_most_k`, `at_least_k`, `exactly_k`).
- Boolean primitives via Tseitin.
- For each: soundness lemma + small unit test.

**Deliverable:** all paper-1 fragment constraints encoded and proven sound.

### M5: leancsp integration (2 weeks)

- Implement `inPBFragment` predicate on `ConstraintPattern`.
- Implement `SatEncodingData` extraction: pattern-match on `csp.domain i` (handle `Set.Icc` for intervals and explicit finite-set literals for sparse domains).
- Implement the full `EncodingResult` builder.
- Implement the full `csp_decide` tactic.
- Test on 3-4 small instances drawn from leancsp's test corpus.

**Deliverable:** any in-fragment leancsp CSP can be discharged via `csp_decide`.

### M6: Test corpus benchmarks (3 weeks)

For each of the 9 Tier-1 families in §10:
- Build the UNSAT variant from the leancsp template.
- Run the pipeline; record metrics.
- Verify the resulting Lean theorem.

For at least 3 families, build a parameterized scaling curve (e.g., QWH for n = 6, 8, 10).

**Deliverable:** benchmark results table with timings; verified Lean theorems for each instance.

### M7: Paper writing (3 weeks)

- Write paper draft.
- arXiv preprint.
- Submit to target venue (AAAI 2027 if August-deadline-compatible; otherwise CPP 2027).

**Total estimate:** ~13–15 weeks for a polished paper-1 deliverable.

---

## 12. Verification strategy

### Proof obligations, in order

1. **`Valuation.intValue_mem_values`** — under monotonicity, recovered values lie in the domain. Foundation for everything else.
2. **`mkLeLit_correct`** — the smart constructor evaluates correctly.
3. **`linear_le_of_threshold_sum`** — the substitution theorem. THE core arithmetic lemma.
4. **`normalize_sat_iff`** — signed-to-natural normalization preserves satisfaction.
5. **Per-constraint soundness lemmas** — each encoder `encodeX_sound : original_constraint_sat → emitted_pb_constraints_sat`.
6. **`PBVar.toNat_injective`** — OPB numbering is well-defined.
7. **`CSPSig.toOPB_unsat`** — OPB-parsed UNSAT implies PB-set UNSAT.
8. **`csp_solution_extends_to_pb_model`** — composition of all encoders' soundness.
9. **`csp_unsat_of_veripb`** — the top-level theorem.

### Things known in advance to be slightly tricky

- **Truncated `Nat` subtraction.** Avoid `Fin (width - 1)` patterns; use `(List.range width).zip (List.range width).tail` over adjacent pairs.
- **`mkLeLit` index arithmetic.** Boundary conditions (k below min, k at/above max) and finding the correct index require careful proof.
- **Big-M computation in `≠` encoding.** Need to prove the bound is tight enough for both implications.
- **Fresh auxiliary tracking.** Use `StateM Nat` for encoders that allocate auxiliaries; close to finite `nAux` before emitting.
- **`SatEncodingData` extraction from arbitrary domain expressions.** For paper 1, restrict to CSPs whose domains are explicit `Set.Icc` or explicit finite-set literals.

### Things to leave as `sorry` initially

When implementing, leave the hard proofs as `sorry` and verify the pipeline runs first. Then come back and discharge proofs one at a time. Specifically:
- All `_sound` lemmas can start as `sorry` while implementing the encoders.
- `toOPB_unsat` can start as `sorry` while implementing serialization.

Don't try to prove everything before the pipeline runs end-to-end; the demo at M3 is more important than full verification at M3.

---

## 13. Known unknowns to validate early

Before committing to the full architecture, verify these three things in M0/M1:

1. **PBLean's reflection API stability.** Confirm `Std.Tactic.BVDecide.LRAT.check`-style API exists in PBLean as documented (`PBLean.Reflect.checkProofBool`, `checkProofBool_sound`). Read `VeriPB/Tactic/Sat/Reflect.lean` source.

2. **RoundingSat + veripb-elaborate produces PBLean-compatible kernel proofs.** Take one of PBLean's existing applications (e.g., the bin packing example), regenerate the OPB and kernel proof from scratch using your local RoundingSat + veripb-elaborate install, and check that PBLean accepts them. This confirms the external toolchain works as PBLean expects.

3. **leancsp `Decidable is_solution` instance performance.** The bridge theorem applies `csp.is_solution a` decidably to a constructed witness in some cases. Confirm that for benchmark-size problems, `decide` or `native_decide` terminates in reasonable time. If not, the bridge theorem proof may need restructuring to avoid the decidable check.

If any of these fail, the implementation strategy needs adjustment before proceeding.

---

## 14. Open design questions

These can be deferred to during-implementation decisions:

1. **`csp_decide` UX.** Two tactic forms: `csp_decide my_csp` (runs full pipeline, slow but self-contained) and `csp_decide_from_files my_csp "x.opb" "x.pbp"` (uses pre-generated files, fast and CI-reproducible). Implement both.

2. **`Fragment.lean` predicate as `Bool` or `Decidable Prop`?** Bool-returning is simpler. Default to that unless a specific use case forces otherwise.

3. **Differential testing.** Run RoundingSat directly on the OPB and confirm it returns UNSAT independently. Useful for catching encoder bugs.

4. **Domain extraction.** For paper 1, restrict to CSPs with explicit `Set.Icc` or finite-set-literal domains. Generic domain shapes (intersections, comprehensions) defer.

5. **Performance baseline.** Compare against the Sugar/CNF/LRAT pipeline on overlapping benchmark instances. Where the comparison is feasible, expect PB to outperform on counting-heavy families (PHP-shaped, Hall-set) and tie or lose elsewhere.

---

## 15. Reference: relevant prior work

### Order-encoding literature

- Crawford & Baker (AAAI 1994), order encoding for scheduling.
- Tamura, Taga, Kitagawa, Banbara, *Compiling finite linear CSP into SAT*, *Constraints* 14(2):254–272, 2009. The foundational order-encoding-to-SAT paper; Sugar is its implementation.
- Abío, Mayer-Eichberger, Stuckey, *Encoding Linear Constraints into SAT*, CP 2015 / arXiv:2005.02073. Uses order encoding + PB rewriting before SAT compilation; closest published technique to the substitution identity in §5.
- Savile Row encoding-selection work, *Constraints* 2023.

### Verified SAT/PB checking in proof assistants

- Heule, Hunt, Kaufmann, Wetzler. *Efficient, verified checking of propositional proofs*. ITP 2017. (LRAT format.)
- Heule, Scheucher. *The empty hexagon theorem*. AAAI 2024. (SAT + verified proof checking for combinatorial geometry.)
- Subercaseaux et al. *Formalizing the SAT encoding of the empty hexagon theorem*. AAAI 2024.
- Gocht, Martins, Myreen, Nordström, Oertel, Tan. *CakePB: end-to-end verified PB proof checking*. 2024. (HOL4/CakeML; standalone binary, no Lean integration.)

### Existing leancsp/PBLean ecosystem papers

- Szeider. *PBLean: Pseudo-Boolean Proof Certificates for Lean 4*. PoS 2026, arXiv:2602.08692. (This is the back end we build on.)
- (leancsp citation TBD — the project is on GitHub; check the README and any associated tech report.)

---

## 16. Quick-start checklist for a new agent

```
☐ Install elan; pin to PBLean's Lean toolchain.
☐ Install RoundingSat (gitlab.com/MIAOresearch/software/roundingsat).
☐ Install VeriPB (gitlab.com/MIAOresearch/software/VeriPB).
☐ Clone PBLean (github.com/leansolving/pblean); `lake build`; run one application end-to-end.
☐ Clone leancsp (github.com/leansolving/leancsp); `lake build`; inspect CSP/Core.lean, CSP/L2S/Core.lean, CSP/L2S/Constraints.lean.
☐ Create new Lake project leancsp-pb with deps on leancsp and pblean.
☐ Follow milestones M0-M7 in order.
☐ At each milestone, run M0's PBLean application test to verify the local toolchain still works.
```

---

## Appendix A: Concrete code structure for the smallest end-to-end demo (M3)

The smallest meaningful demo is: `x, y, z ∈ {0..3}` with `x + y + z ≤ 2 ∧ x + y + z ≥ 5` (clearly UNSAT — the sum is bounded below by 0 and above by 9, but the two constraints together require it to be both ≤ 2 and ≥ 5).

```lean
-- Tests/Demo.lean
import LeancspPB

namespace LeancspPB.Tests

/-- The toy CSP signature: 3 integer vars, no Booleans, no auxiliaries, all domains [0..3]. -/
def demoSig : CSPSig where
  nInt := 3
  nBool := 0
  nAux := 0
  values := fun _ => [0, 1, 2, 3]
  sorted := by intro _; decide
  nonempty := by intro _; decide

/-- Pre-generated artifacts (created in M3 by running the encoder + RoundingSat + veripb). -/
-- artifacts/demo.opb     : the OPB file
-- artifacts/demo.kernel.pbp : the elaborated kernel proof

theorem demo_unsat :
    ¬ ∃ x y z : Fin 4,
      x.val + y.val + z.val ≤ 2 ∧ x.val + y.val + z.val ≥ 5 := by
  -- Stage 1 (M3 minimum): construct EncodingResult by hand.
  -- Stage 2 (M5 full): replace with csp_decide on a HomogeneousCSP definition.
  csp_decide_from_files
    "artifacts/demo.opb"
    "artifacts/demo.kernel.pbp"

end LeancspPB.Tests
```

This goal mentions `Fin 4` directly. For M3, the bridge to leancsp's `HomogeneousCSP` is hand-crafted; M5 generalizes.

---

## Appendix B: How PBLean's existing applications work (reference pattern)

Looking at `VeriPB/Tactic/Sat/IndependentSet.lean` (in the PBLean source), the pattern for a verified application is:

```lean
-- 1. Define a problem-specific predicate.
def independentSet (G : Graph) (S : Finset Nat) (k : Nat) : Prop := …

-- 2. Define an encoding function: problem instance → PB constraints.
def encodeIS (G : Graph) (k : Nat) : List (PBConstr Nat) := …

-- 3. Prove encoding soundness: PB UNSAT ⇒ no independent set of size ≥ k.
theorem encodeIS_sound (G : Graph) (k : Nat) :
    (PBSet.Unsat (encodeIS G k)) → ¬ ∃ S, independentSet G S k := …

-- 4. Provide a bridge command: given OPB file and proof, discharge the theorem.
elab "independent_set_decide" g:term k:term name:ident opb:str pbp:str : command => …

-- 5. Apply for specific instances.
independent_set_decide (paley 13) 4 paley13_alpha_upper
  "applications/paley/Paley_13.opb"
  "applications/paley/Paley_13_kernel.pbp"
```

Our generic pipeline reuses this pattern but parameterizes over the *problem* via `HomogeneousCSP` rather than hardcoding per-problem encoders. The `csp_decide` tactic is to leancsp CSPs what `independent_set_decide` is to Paley graphs.

---

## Appendix C: leancsp test files for benchmark generation

To find UNSAT-variant benchmark instances, start from these existing files in leancsp:

| File | Use for |
|------|---------|
| `CSP/L2S/Tests/lean/02_color.lean` | Pre-colored graph k-coloring UNSAT |
| `CSP/L2S/Tests/lean/07_latin_squares.lean` | QWH benchmark family |
| `CSP/L2S/Tests/lean/08_queens.lean` | N-Queens with forbidden cells |
| `CSP/L2S/Tests/lean/10_langford_simple.lean` | Langford pairing UNSAT (n ≡ 2, 3 mod 4) |
| `CSP/L2S/Tests/lean/11_schur.lean` | Schur triples (n > S(k) UNSAT) |
| `CSP/L2S/Tests/lean/12_graph.lean` | Graph coloring |
| `CSP/L2S/Tests/lean/15_golomb.lean` | Golomb ruler UNSAT for short lengths |
| `CSP/L2S/Tests/lean/17_all_interval.lean` | All-interval series UNSAT |
| `CSP/L2S/Tests/lean/18_costas.lean` | Costas arrays |
| `CSP/L2S/Tests/lean/19_sudoku.lean` | Sudoku with adversarial clues |

For each, the procedure is:
1. Copy the leancsp template into a new test file in `LeancspPB/Tests/`.
2. Add `ne_const`/`eq_const` constraints for the UNSAT variant.
3. Apply `csp_decide` (or `csp_decide_from_files` once the pipeline is stable).
4. Verify the resulting Lean theorem.

---

## End of plan

The new agent has now read everything needed. Start with M0; do not skip any of the validation checks in §13. If any of them fail, surface the failure and re-plan before continuing.
