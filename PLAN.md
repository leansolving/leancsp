# LeanCSP PB backend — implemented status, architecture, and results

This document records the **as-built state** of the verified pseudo-Boolean (PB)
UNSAT-certificate backend. The original from-scratch implementation plan (the
M0–M7 milestone breakdown, dependency list, and reference literature) is preserved
in **`PLAN_old.md`**; this file supersedes it as the status/architecture summary.

- **What the backend does and how to use it:** top-level `README.md`.
- **How to add a new UNSAT instance:** `docs/ADDING_UNSAT_INSTANCES.md`.
- **This file:** what is implemented, how it is structured, the results, how the
  implementation diverged from the original plan, and what remains.

---

## 1. Status

The verified pipeline is **complete and integrated**. Every module under
`CSP/L2S/Backends/PB/` builds with **zero `sorry`**, and a bare `lake build`
(via the `globs := #[.andSubmodules \`CSP]` lakefile setting) compiles and
re-checks the entire backend, whose kernel proofs are re-validated by
`native_decide` during the build.

**The single generic theorem (current state).** The backend has been refactored so
that *one* soundness theorem discharges every instance:

- **`Int` nomenclature.** `HomogeneousCSP` → `IntCSP`, satisfaction is now
  pattern-determined (`satisfiesConstraintInt c a := patternHolds c a`), making a
  generic encoder possible (`CSP/L2S/Core.lean`).
- **`csp_unsat csp cert : ¬ csp.isSatisfiableInt`** (`GenericEncode.lean`) — derives
  the signature (`cspSig`), the PB formula (`encodeCSP`, via `encodePattern`
  dispatching the `IntConstraint` inductive to the per-pattern encoders), and all
  preconditions automatically; no per-instance soundness. `encodePattern_sound`
  feeds each constraint's `patternHolds` into its library soundness lemma.
- **File-based certificates.** `csp_unsat_file csp numVars "certs/foo.pbp"`
  (`include_str` + `native_decide`) replaces inline kernel-proof strings;
  `scripts/gen_cert.sh` regenerates them against `encodeCSP`. Corpus instances moved
  to `CSP/L2S/Backends/PB/Problems/` with certificates under `Problems/certs/`.
- **22 problem theorems** (all aux-free families: `alldifferent`, `not_equal`,
  `eq_const`, `ne_const`, `at_most_k`, `at_least_k`, `linear`, `sum`,
  `schur_triple`) are now one-line `csp_unsat_file`. The remaining 6 (N-Queens /
  blocked queens, the circuit family, full-adder / ripple-carry) keep bespoke proofs
  until their encoders are wired into `encodePattern` (§6).
- The deferred `CSP/L2S/Proofs/` experiments (equivalence + symmetry-breaking) were
  removed; the whole project is green.

| Milestone (from `PLAN_old.md`) | State |
|---|---|
| **M0** Project setup, external toolchain validated | Done. Dependency on PBLean (`veripb` Lake pkg, pinned `v0.3.0`); RoundingSat + veripb 3.0.1 validated end-to-end. |
| **M1** Core types (`CSPSig`, `PBVar`, `mkLeLit`, `intValue`, monotonicity) | Done; `intValue_mem_values` proved. |
| **M2** Substitution theorem (`linear_le_of_threshold_sum`) | Done. |
| **M3** Linear encoding + smallest end-to-end demo | Done (`Demo.lean`, `DemoGeneric.lean`, `DemoHomogeneous.lean`). |
| **M4** Remaining encodings (`=,≥,<,>`, `≠`, alldifferent, cardinality, Boolean) | Done — all paper-1 fragment families implemented and proved sound. |
| **M5** leancsp integration (generic spine + adapter + tactic) | Done (`Extend.lean`, `Adapter.lean`, `Tactic.lean`). |
| **M6** Test-corpus benchmarks | Realized as **29 committed end-to-end theorems** across 16 problem families (§4), plus the cutting-planes-vs-resolution **scaling study** in `docs/SCALING.md`. |
| **M7** Paper | Future work (not in this repo). |

**Toolchain.** Pinned in `lean-toolchain` (`leanprover/lean4:v4.30.0`); Mathlib,
`Canonical`, and `veripb` (PBLean) pinned in `lake-manifest.json`.

---

## 2. Architecture

### The pipeline

```
IntCSP  (Lean; a corpus CSP, e.g. php_3_2)
   │  order encoding — VERIFIED IN LEAN
   │  integer var x with domain D  ↦  threshold bits  "x ≤ dⱼ"
   ▼
PB constraints over typed threshold variables  (PBVar S)
   │  toNat injection  →  PBLean's Sat.PB.Constr   (VERIFIED IN LEAN)
   ▼
OPB file  ──[ RoundingSat, UNTRUSTED ]──▶  VeriPB proof
                                              │  [ veripb --elaborate, UNTRUSTED ]
                                              ▼
                                           kernel proof  (committed as Problems/certs/*.pbp,
                                                          loaded via include_str)
   │  PBLean checker  checkProof_sound  (VERIFIED IN LEAN; run by native_decide)
   ▼
formulaUnsat  ──[ csp_unsat soundness theorem ]──▶  ¬ csp.isSatisfiableInt
```

### Module map (`CSP/L2S/Backends/PB/`, namespace `CSP.L2S.PB`)

**Core / semantics**
- `CSPSig.lean` — the encoder's variable signature (`nInt`/`nBool`/`nAux`, per-var
  `values`, `width`, `gap`, `maxVal`).
- `PBVar.lean` — the typed propositional variable (`bool`/`thr`/`aux`); `LitConst`
  and the smart constructor `mkLeLit` for "x ≤ k".
- `PBConstr.lean` — a polymorphic mirror of PBLean's monomorphic `Sat.PB.Constr`,
  so the encoder works over typed variables and the `Nat` arithmetic is localized
  to one bridge file.
- `Semantics.lean` — `intValue`, `orderConsistent`, `monotonicity` (staircase
  clauses), and the foundational lemma `intValue_mem_values` (recovered value lies
  in the declared domain) plus `intValue_switch`.
- `Substitution.lean` — `linear_le_of_threshold_sum`, the one load-bearing
  arithmetic identity converting a linear CSP constraint into a linear PB
  constraint over threshold bits.

**Encoders** (each with a Lean soundness lemma)
- `SignedPB.lean` — signed→natural normalization (`normalize`, `normalize_sat_iff`).
- `Encode.lean` — `encodeLinearLe` (+ `Ge/Lt/Gt/Eq` wrappers).
- `AllDifferent.lean` — `encodeAllDifferent` (per-value cardinality), `encodeNeConst`,
  multi-valued not-all-equal.
- `Cardinality.lean` — `encodeAtMostK` / `AtLeastK` / `ExactlyK`.
- `LinearNe.lean` — general `Σ aᵢxᵢ ≠ b` via a Big-M aux selector (the only
  aux-allocating encoder used).
- `NotAllEqual.lean` — literal-level and binary not-all-equal.
- `BoolGates.lean`, `BoolExprCompiler.lean` — Tseitin gate primitives and a
  recursive `BoolExpr` compiler (verified; see §5 — no current consumer).
- `CircuitGates.lean` — `{nv}`-generic circuit gate bridges (`xor_all3_sat`,
  `and_gate_sat`, `or_all3_full_sat`, the pure-ℤ `fa_identity`).

**Bridge to PBLean + spines**
- `ToNat.lean` — `toNat` injection (`toNat_injective`), `toNatConstr`, and
  `unsat_bridge` (PBLean's `formulaUnsat` ⇒ no typed valuation satisfies all).
- `Extend.lean` — `extend` (order-encode a CSP assignment into a valuation) and the
  generic spine `csp_unsat_generic` (aux-aware) plus its aux-free specialization
  `csp_unsat_of_linear`.
- `Adapter.lean` — `domainValues`, `toCSPSig`, the pattern→fact bridges
  (`bound_sat`, `linear_le_sat`, `at_most_k_sat`, …), and the clean linear-list
  spine `unsat_of_pb`.
- `NotAllEqualBridge.lean` — shared, test-file-free bridges (`alldifferent_sat`,
  `not_equal_sat`, `equals_const_sat`, `schur_triple_sat`, and the matching
  `extend_sat_*` soundness lemmas).

**Generic pipeline (the single `csp_unsat`)**
- `Compose.lean` — `EncConstr` (a soundness-carrying encoded constraint: its PB
  constraints, its arithmetic precondition, the aux it owns, and a `sound` proof)
  and the assumption-free composition `csp_unsat_of_enc` / `csp_unsat_of_encfree` /
  `csp_unsat_of_enc_alloc` (the last with an automatic aux-index allocator).
- `Library.lean` — one `enc<Pattern> : … → EncConstr S` per supported family,
  bundling its encoder with its per-constraint soundness.
- `GenericEncode.lean` — `cspSig` (signature from the CSP's `bound`s), `toFinList`
  (ℕ→`Fin` index conversion), `encodePattern` (`IntConstraint` → `EncConstr` list,
  via the per-pattern library), `encodePattern_sound` (each entry's `pre` from
  `patternHolds`), `encodeCSP`, the generic theorem **`csp_unsat`**, and the
  **`csp_unsat_file`** macro (`include_str` + `native_decide`).

**Serialization + tactic**
- `Serialize.lean` — OPB text serializer (untrusted; outside the trust base).
- `Tactic.lean` — `csp_reflect_unsat` (reads a committed kernel proof, discharges
  `formulaUnsat`) and `csp_decide` (shells out at elaboration — non-hermetic). The
  preferred entry point is now `csp_unsat_file` (`GenericEncode.lean`).
- `scripts/gen_cert.sh` — regenerate a `Problems/certs/*.pbp` against `encodeCSP`.

### Trust boundary

Trusted: Lean's kernel; PBLean's reflection checker (`checkProof_sound`, proved in
Lean, run via `native_decide` — places the Lean compiler in the TCB through
`Lean.ofReduceBool`, the same shape as `bv_decide`); and this backend's
order-encoder soundness theorems. Untrusted: RoundingSat, veripb, and the OPB
serializer — a fault in any of them causes a *failure to elaborate*, never an
unsound theorem. Every end-to-end theorem's `#print axioms` is exactly `propext,
Classical.choice, Quot.sound` plus one `native_decide` axiom — no `sorryAx`.

---

## 3. Soundness spines

The top-level entry point is **`csp_unsat`** (`GenericEncode.lean`, §1), which builds
the encoding and composes it automatically. It is built on the lower-level spines
below, which the `EncConstr` composition (`Compose.lean`) and the older bespoke
proofs share; the same encoder output is composed into `¬ isSatisfiableInt` through
one of them:

- **`csp_unsat_generic`** (`Extend.lean`) — the general spine. The caller supplies
  the PB constraints, a solution predicate `P`, an aux-setter `auxOf`, and per-
  constraint soundness (`hsound`). The spine owns the monotonicity clauses and the
  PBLean bridge. Required when the encoding allocates auxiliary variables (Big-M
  `≠`), because `auxOf` sets them from the solution.
- **`unsat_of_pb`** (`Adapter.lean`) — the clean route for problems that are purely
  linear `≤`-constraints over uniform interval domains (e.g. Paley independent
  set). The caller supplies bounds, a linear-constraint list, and the derivations;
  the adapter builds the signature and encoding.

---

## 4. Results — end-to-end UNSAT theorems

Across 16 problem families (full table with module/corpus in `README.md`). **22**
are now one-line `csp_unsat_file` over committed certificates (every aux-free
family); the remaining **6** (N-Queens / blocked queens, the circuit family,
full-adder / ripple-carry) keep bespoke proofs until their encoders are wired into
`encodePattern` (§6). Six are scaling checkpoints from the `docs/SCALING.md` study —
the larger pigeonhole, mutilated-chessboard, and odd-cycle instances:

- **Pigeonhole** — `php_3_2_unsat`, `php_5_4_unsat`, `php_7_6_unsat`, `php_9_8_unsat`.
- **Schur** — `schur_2_5_unsat` (2-colour), `schur_3_14_unsat` (3-colour).
- **Van der Waerden** — `vdw_2_3_9_unsat`. **Ramsey** — `ramsey_3_3_K6_unsat`.
- **Graph colouring** — `k3_2col_unsat`, `k4_3col_unsat`, `k2_forbidden_unsat`;
  odd cycles `c5_2col_unsat`, `c7_2col_unsat`, `c9_2col_unsat` (the
  2-colourability scaling baseline).
- **N-Queens** — `nqueens_2_unsat`, `nqueens_3_unsat`.
- **Langford** — `langford_2_2_unsat`.
- **Sudoku / Latin square (contradictory givens)** —
  `sudoku_4_contradictory_unsat`, `latin_2_contradictory_unsat`.
- **Circuit verification** — `full_adder_correct_unsat`,
  `ripple_carry_4bit_correct_unsat`, `xor_equivalence_unsat`,
  `circuit_majority3_unsat`.
- **Independent set** — `paley_13_4_unsat` (α(Paley(13)) ≤ 3 — a genuine
  combinatorial theorem, certified by a non-trivial cutting-planes proof).
- **Magic hexagon** — `magic_hexagon_2_unsat` (no order-2 normal magic hexagon;
  the divisibility obstruction `3·M = 28`).
- **Mutilated chessboard** — `mutilated_chessboard_unsat` (4×4 minus two
  same-colour corners has no domino tiling; the colour-counting argument) and
  `mutilated_chessboard_6_unsat` (the 6×6 scaling checkpoint).
- **Peaceable armies of queens** — `peaceable_armies_4_3_unsat`
  (`a(4) = 2`, so 3 + 3 peaceable queens on the 4×4 board is infeasible).
- **Blocked N-Queens** — `blocked_queens_4_unsat` (4-queens with the first
  column forbidden in every row; a column pigeonhole).

The last four are modelled directly (not pre-existing corpus problems), except
the blocked-queens instance, which reuses the corpus `nqueens_csp 4` model plus
blocking constraints.

**Supported constraint fragment.** Linear arithmetic (`≤,≥,=,<,>`); disequality
`≠` (aux-free for var≠const and var≠var, Big-M for general linear `≠`);
`alldifferent`; cardinality (`at_most_k`, `at_least_k`, `exactly_k`); not-all-equal
(binary and multi-valued); Boolean/circuit gates (AND/OR/XOR over `{0,1}`, handled
as linear or via the full-adder identity). **Out of scope:** non-linear constraints
(`product_eq_var`), and the global constraints deferred in the original plan
(`element`, `table`, `regular`, `circuit`, `cumulative`).

---

## 5. How the implementation diverged from the original plan

For a reader comparing against `PLAN_old.md`, the substantive design decisions:

1. **Real PBLean API.** The plan's aspirational names (`PBConstr`, `OPBFormula`,
   `checkProofBool_sound`) do not exist under those names. The real kernel API is
   `Sat.PB.Constr` (monomorphic, `Nat` vars/coeffs), `VeriPB.Reflect.formulaUnsat`,
   and `VeriPB.Reflect.checkProof_sound`. The encoder uses a polymorphic mirror
   `PBConstr V` and bridges to `Sat.PB.Constr` in `ToNat.lean`.
2. **Typed `PBVar` core (plan's "Option A").** Constraints are built over a typed
   variable type (`bool`/`thr i j`/`aux`), not raw `Nat`, so "only valid thresholds
   exist" holds by typing and all offset arithmetic is confined to `ToNat.lean`.
3. **`alldifferent` via per-value cardinality, not reified `≠`.** The plan sketched
   multi-valued not-all-equal as a disjunction of reified disequalities; the
   aux-free per-value form (`∀ val: Σⱼ⟦xⱼ=val⟧ ≤ |vars|−1`) is simpler and reuses
   the alldifferent machinery. The reified-`≠` primitive was therefore unnecessary.
4. **Circuits are linear, not Tseitin.** AND/OR over `{0,1}` are min/max (linear);
   2-input XOR is exactly four linear inequalities; 3-input parity is captured by
   the pure-ℤ full-adder identity `fa_identity`. So all four circuit theorems
   (full adder, ripple-carry, XOR equivalence, majority) ride `encodeLinearLe`/
   `encodeNeConst` with **no** Tseitin/BoolExpr machinery.
5. **Two spines** (`csp_unsat_generic` + `unsat_of_pb`) rather than one monolithic
   `csp_unsat_of_veripb` — the aux-free linear route is markedly shorter.
6. **Certificates committed inline.** Each instance embeds its kernel proof as a
   `String` and discharges `formulaUnsat` with `checkProof_sound … (by
   native_decide)`. This makes every theorem reproducible from Lean + the Mathlib
   cache alone (no solvers needed to re-check). `csp_decide` (full shell-out) and
   `csp_reflect_unsat` (reads a `.pbp` file) also exist but are not how the
   committed theorems are stated.

---

## 6. Remaining work — covering all constraints and problems

The goal is for **every** finite-domain CSP in the supported modeling fragment to be
discharged by the one-line `csp_unsat_file`. All remaining work is local to
`encodePattern` / the encoder library — **never per-problem**. After each item, the
affected instances collapse to one-liners with regenerated certificates.

1. **`alldifferentOffset`** (diagonal all-different — N-Queens, blocked queens): add
   an offset-aware encoder `encodeAllDifferentOffset` (per-value cardinality over the
   shifted values `a vᵢ + offsetᵢ`) + soundness, then one `encodePattern` case.
   Migrates `nqueens_*`, `blocked_queens_4`.
2. **Boolean gates** (`and_gate`/`or_gate`/`not_gate`/`xor_*`/`and_all`/`or_all`):
   emit the linear `{0,1}` encodings (`out ≤ inᵢ`, `out ≥ Σ inᵢ − (k−1)`, parity via
   the full-adder identity) as `EncConstr`s, derive their preconditions from
   `patternHolds`. Migrates the circuit family (`xor_equivalence`, `circuit_majority3`).
3. **Big-M general linear `≠`** (`linear_ne`): wire `encLinearNe` (owns one aux
   selector) into `encodePattern`, switch `csp_unsat` from `csp_unsat_of_encfree` to
   `csp_unsat_of_enc_alloc`, and size `cspSig.nAux` to the number of `≠` constraints
   (the allocator already builds the global aux assignment from pairwise-distinct
   owned indices). Migrates `full_adder`, `ripple_carry`.
4. **The remaining `IntConstraint` constructors** (`count`, `element`,
   `maximum`/`minimum`, `modulo`, `abs_diff_*`, `increasing`, `implies`/`iff`,
   `*_rel_var`, …): each is one `encodePattern` case + a soundness lemma over an
   encoder; genuinely non-linear ones (e.g. `product_rel_var`,
   `30_multiplier_verification`) stay `[]` (sound by weakening) and are out of the
   PB fragment.
5. **Scaling** — larger corpus sizes (wider ripple-carry, larger Paley graphs —
   probe UNSAT status with RoundingSat first) and a `scripts/gen_cert.sh` sweep over
   all instances whenever an encoder changes shape.

**Unmotivated / optional:** the recursive `BoolExpr` Tseitin compiler
(`BoolExprCompiler.lean`) is verified but has no consumer — every circuit goes
through the linear/identity route; integrating it into the spine is optional.
