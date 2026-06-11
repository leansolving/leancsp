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
- **`csp_sat_pb_sat`** (`GenericEncode.lean`) — the headline soundness theorem,
  **CSP-SAT ⇒ PB-SAT**: every satisfiable `IntCSP` (each variable carrying a `bound`)
  has a satisfiable PB encoding, witnessed by order-encoding the solution with the
  Big-M selectors set by the generic allocator.  No per-instance hypotheses —
  selector distinctness is proven once, generically (`encodeCSP_keys_nodup`, a
  structural induction over the threaded selector blocks).
- **`csp_unsat csp cert : ¬ csp.isSatisfiableInt`** — the contrapositive of
  `csp_sat_pb_sat` instantiated with a kernel-checked certificate; derives the
  signature (`cspSig`, aux-sized by `cspNAux`), the PB formula (`encodeCSP`, via the
  selector-base-threaded `encodePatternAt`), and all preconditions automatically.
- **File-based certificates.** `csp_unsat_file csp numVars "certs/foo.pbp"`
  (`include_str` + `native_decide`) replaces inline kernel-proof strings;
  `scripts/gen_cert.sh` regenerates them against `encodeCSP` (its `numVars` counts
  thresholds *plus* Big-M selectors). Corpus instances live in
  `CSP/L2S/Backends/PB/Problems/` with certificates under `Problems/certs/`.
- **All 28 problem theorems are one-line `csp_unsat_file`** — including the formerly
  bespoke N-Queens / blocked queens (via `alldifferentOffset`'s pairwise Big-M
  expansion), the circuit family (Boolean-gate facet encodings), and full-adder /
  ripple-carry (ternary-XOR parity-polytope facets + the Big-M `≠` identity).
- Every end-to-end theorem's axioms: `propext, Classical.choice, Quot.sound` plus
  exactly **one** `native_decide` (the certificate recheck); no `sorryAx`.
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

Across 16 problem families (full table with module/corpus in `README.md`). **All 28**
are one-line `csp_unsat_file` over committed certificates — no bespoke proofs remain;
every theorem is `csp_unsat` (the certificate-instantiated contrapositive of the
general soundness theorem `csp_sat_pb_sat`). Six are scaling checkpoints from the
`docs/SCALING.md` study — the larger pigeonhole, mutilated-chessboard, and odd-cycle
instances:

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

**Done (the generic-coverage push).**  All 28 committed problems are one-line
`csp_unsat_file`; no bespoke proofs remain.  `encodePatternAt` covers, with
per-constructor soundness: the linear/cardinality relations (`linear`, `sum`,
`exactly_k`, `at_most/least_k`, binary `eq/ne/lt/le/gt/ge`, the `*_const`
comparisons, `implies`, `iff`, `sum_rel_var`, `linear_rel_var` — `.NE` variants via
the Big-M selector), `alldifferent`, `alldifferentOffset` (pairwise Big-M expansion),
`schur_triple`, the Boolean gates (`not/and/or/xor/nand/nor_gate`, `and_all`,
`or_all`, `xor_all` of arity 2 and 3 — min/max facets and the parity-polytope
facets), `increasing` (consecutive `≤` chain), and `maximum`/`minimum` (the implied
per-element bounds; the attainment disjunct is dropped, sound by weakening).

**Also covered (the constraint-completion push).**  `sliding_sum` (one linear relation
per window), `if_then`/`if_then_or` (indicator-implication facets, aux-free exact),
`count` (indicator-sum equality) and `count_var` (gated cardinality per domain value of
the target), `maximum`/`minimum` *attainment* (per-domain-value facets
`[mx = d] ≤ Σᵥ ⟦v ≥ d⟧` over single threshold literals — now exact, not a relaxation),
`modulo` (domain filter: `≠`-const per wrong-residue value — exact), `element` (index
bounds + one `if_then` implication per position), and the full `abs_diff_rel` /
`abs_diff_var` family (bounds for `≤`/`<`; the generic gated disjunction `encodeOrLe`
with one Big-M selector for `≥`/`>`/`=` and attainment; two `≠`-selectors for `≠`;
trivial/infeasible thresholds handled exactly).

**Remaining constructors (all that is left).**
1. **`xor_all` of arity ≥ 4** — `[]`. Wide parity is standardly modelled as a chain of
   ternary gates in the CSP itself (what the corpus adders do); a PB-level parity chain
   would need mixed threshold/aux-literal constraint machinery with no current consumer.
2. **`product_rel_var`** — `[]`, genuinely non-linear; out of the PB fragment.
3. **`disjunctive` / `unknown`** — `patternHolds` is `True`, so `[]` is *exact* (nothing
   to encode).
4. Gates over non-`{0,1}` domains are dropped by their decidable domain guards (sound).
5. **Scaling** — larger corpus sizes (wider ripple-carry, larger Paley graphs —
   probe UNSAT status with RoundingSat first) and a `scripts/gen_cert.sh` sweep over
   all instances whenever an encoder changes shape.

**Unmotivated / optional:** the recursive `BoolExpr` Tseitin compiler
(`BoolExprCompiler.lean`) is verified but has no consumer — every circuit goes
through the linear/identity route; integrating it into the spine is optional.

---

## 7. Dead code — left behind by the generic refactor

The move to the single generic `csp_unsat` / `csp_unsat_file` (the `IntConstraint` +
`patternHolds` + `encodeCSP` pipeline of §1–§3) made several modules and
definitions obsolete. They were **not** deleted in the refactor, so they still sit in
the tree. This matters in practice: the lakefile's `globs := #[.andSubmodules
\`CSP]` compiles **every** file under `CSP/` regardless of whether anything imports
it, and the dead Boolean modules still re-run their `native_decide` checks — so this
is dead weight on every `lake build`, not merely unreferenced source. Verified
against the import graph on `csp-unsat-generic`:

**Pure dead pair (no consumer anywhere) — first to remove.**
- `Backends/PB/BoolExprCompiler.lean` — recursive Tseitin compiler; imported by **0**
  files. Every circuit theorem goes through the linear / `fa_identity` route, so it
  never had a consumer (already flagged "Unmotivated / optional" in §6).
- `Backends/PB/BoolGates.lean` — Tseitin gate primitives (`gateNot`/`gateAnd`/…);
  imported by exactly **one** file, `BoolExprCompiler.lean`, which is itself dead.
  Transitively dead; removing the pair together is clean.

**Legacy tactics superseded by `csp_unsat_file`.**
- `csp_decide` in `Backends/PB/Tactic.lean` (plus its helpers `evalOPB` /
  `evalOPBUnsafe`) — the non-hermetic shell-out variant. No committed theorem uses
  it; its only mention is a comment in `Serialize.lean`.
- `csp_reflect_unsat` in `Backends/PB/Tactic.lean` — reads a `.pbp` file and
  discharges `formulaUnsat`. Its only caller is the demo `DemoReflect.lean`. The
  committed theorems all use `csp_unsat_file` (`include_str` + `native_decide`)
  instead.

**Demonstration scaffolding (illustrative, off the problem pipeline).**
- `Backends/PB/Demo.lean`, `DemoGeneric.lean`, `DemoHomogeneous.lean`,
  `DemoReflect.lean` — these only import each other (`Demo` ← `DemoGeneric` ←
  `DemoHomogeneous`; `DemoReflect` standalone) and are imported by no problem or
  spine. They document the old hand-wired route (build `phpSig`/`phpEncoded` by
  hand, inline `String` certificate, compose through a spine) that the generic
  pipeline replaced. `Demo.lean` predates `Problems/`.
- `Backends/PB/Serialize.lean` (`toOPBString`) — the untrusted OPB text serializer.
  Outside the trust base. Its only in-Lean users are the demo cluster and the dead
  `csp_decide`; its real consumer is the **external** `scripts/scaling/validate.py`
  byte-identity check, so it cannot be deleted outright — see the scaling-harness
  caveat below.

**Newly dead since the generic-coverage push (all 28 problems now one-line).**
- `Backends/PB/CircuitGates.lean` — the circuit-gate semantic bridges
  (`and_gate_sat`, `or_all3_full_sat`, `xor_all3_sat`, `fa_identity`).  Its only
  consumers were the bespoke FullAdder/RippleCarry proofs, now deleted; **0**
  importers remain.  Removable with the same care as the Boolean pair above.
- `unsat_of_pb` (`Adapter.lean`) — the clean linear spine no longer has any problem
  consumer (only the demo cluster references it).  The *module* stays (it defines
  `toCSPSig`/`domainValues`, which `cspSig` builds on); only the spine def is dead.
- `csp_unsat_generic` (`Extend.lean`) keeps one structural consumer — the
  `EncConstr` composition (`Compose.lean`) is proven through it — so it is plumbing,
  not dead.

**Still live — do NOT remove.** All encoder soundness modules (`Encode`,
`AllDifferent`, `Cardinality`, `LinearNe`, `NotAllEqual`, `NotAllEqualBridge`),
the generic layer (`Compose` / `Library` / `GenericEncode`), and `Core` (pulled in
by the live `ToNat` bridge) are all reachable from the generic composition.

### Removal plan (staged, lowest-risk first)

1. **Delete the dead Boolean pair** `BoolExprCompiler.lean` + `BoolGates.lean`
   together. Zero importers, so a bare `lake build` is the only check needed. This
   also reclaims their `native_decide` recheck time. (If the Tseitin route is ever
   wanted — §6 "optional" — recover it from git history.)
2. **Strip the legacy tactics** `csp_decide` (+ `evalOPB` / `evalOPBUnsafe`) and
   `csp_reflect_unsat` from `Tactic.lean`, and drop the stale `csp_decide` comment in
   `Serialize.lean`. This makes `DemoReflect.lean` dead (its only content is a
   `csp_reflect_unsat` call), so remove it in the same step.
3. **Remove the remaining demo cluster** `Demo.lean` / `DemoGeneric.lean` /
   `DemoHomogeneous.lean` once nothing else imports them. If a worked example is
   still wanted for docs, replace the cluster with a single short `csp_unsat_file`
   example under `Problems/` rather than the hand-wired version.
4. **Keep `Serialize.lean`** until the scaling harness is ported (it backs
   `validate.py`'s byte-identity assertion). If/when the scaling scripts are updated
   to elaborate `encodeCSP` directly, re-evaluate whether `toOPBString` still has any
   consumer.

After each stage: `lake build` (the `andSubmodules` glob rebuilds everything) and a
`#print axioms` spot-check on a representative end-to-end theorem to confirm the
trust base is unchanged (`propext, Classical.choice, Quot.sound` + one
`native_decide` axiom).

---

## 8. Scaling harness — port to the generic pipeline

**Status: DONE (as-built).** All five fix-plan steps below are implemented: the
harness targets the generic pipeline (`cspSig`/`encodeCSP`, `Problems/` modules,
`csp_unsat_file` + `certs/*.pbp`), `validate.py` reports ALL IDENTICAL on 9 cases
(php n=2,4,6,8; mutilated k=2,3; odd-cycle C₅,C₇,C₉ — `pbgen.py` needed only an
odd-cycle clause-order swap), `gen_mutilated_lean.py` emits the one-line module
*and* its certificate (from pbgen's OPB via RoundingSat + veripb, breaking the
module↔cert chicken-and-egg) and reproduces the committed `MutilatedChessboard6.lean`
byte-for-byte, and the full sweep + in-Lean timings were re-run on the Linux
machine (`results/scaling*.csv`, SCALING.md tables refreshed). `Serialize.lean`
survives: `toOPBString` still backs `validate.py` and `gen_cert.sh`.

The cutting-planes-vs-resolution scaling study (`docs/SCALING.md`, `scripts/scaling/`,
`results/scaling*.csv`) was authored against the **pre-refactor** pipeline (the
hand-wired `phpSig`/`phpEncoded`, inline-`String` certificates, and per-instance
modules of §5/§7). The scripts were carried onto this branch **unchanged** — they were
byte-identical to the `cert` branch — so they no longer matched the Lean they point at.
This was the same class of staleness as §7, but on the external (Python) side; the
unfinished tail of §6 item 5 ("Scaling").

The right time to fix it is **once the generic pipeline covers all problems** (after
§6.1–§6.4, when every family is a one-line `csp_unsat_file` and the bespoke proofs
and the two spines are gone). Porting earlier means re-porting after each encoder
reshape; porting once the encoder shape is final does it once.

### What is broken (verified against `csp-unsat-generic`)

1. **`scripts/scaling/lean_timing.py`** hardcodes the old module paths and ids —
   `CSP/L2S/Backends/PB/Pigeonhole.lean`, module `CSP.L2S.Backends.PB.Pigeonhole`,
   and likewise `MutilatedChessboard6`, `OddCycle`. All three modules now live under
   `Backends/PB/Problems/` (module id `…Backends.PB.Problems.Pigeonhole`), so every
   import/recheck it builds fails to resolve. Its cost model is also stale: it splits
   "native_decide recheck vs. module build" assuming an **inline `String`**
   certificate, but the theorems now load the cert from `certs/*.pbp` via
   `include_str`.
2. **`scripts/scaling/validate.py`** elaborates per-instance encoder symbols that no
   longer exist — `Pigeonhole.phpEncoded`, `php5Encoded`, `MutilatedChessboard.mcSig`,
   `mcLin` (all **0 occurrences** now). They were absorbed into the generic
   `cspSig` / `encodeCSP` / `encodePattern`. The serializer it drives (`toOPBString`)
   still exists, so the mechanism survives — only the expressions it feeds in must
   change.
3. **`scripts/scaling/gen_mutilated_lean.py`** (the new-checkpoint generator) emits a
   template incompatible on every axis: `¬ …​.isSatisfiable` (now `isSatisfiableInt`),
   `HomogeneousAssignment` (now the `Int` nomenclature), an inline `mcKernelProof :
   String`, and bespoke `mc_hbound` / `mc_hlin` / `mc_formulaUnsat` lemmas — none of
   which match the one-line `csp_unsat_file` + `certs/*.pbp` form.
4. **`scripts/scaling/pbgen.py`** must be re-checked for **byte-for-byte identity**
   against the generic `encodeCSP` output. If the generic encoder changed variable or
   constraint ordering or normalization, the standalone OPB drifts from what the Lean
   theorems check — which would also mean the committed `cert (chars)` columns in the
   CSVs no longer match certs regenerated by `scripts/gen_cert.sh`.

### Fix plan (after the pipeline covers all problems)

1. **Repoint `lean_timing.py`** at `Backends/PB/Problems/<Family>.lean` and the
   `…Backends.PB.Problems.<Family>` module ids. Replace the recheck-cost expression
   with the `csp_unsat_file` / `include_str` form. With every family now generic and
   sharing one `csp_unsat` proof, the §5 finding ("what grows in-Lean is the
   soundness-bridge proof, not the recheck") changes shape — the per-family bridge is
   gone, so re-measure and rewrite SCALING.md §5 to report the *generic* recheck +
   `encodeCSP` elaboration cost instead of bespoke `mc_hlin`-style bridges.
2. **Rewrite `validate.py`'s `lean_opb_expr`s** to serialize the generic encoding —
   `toOPBString (encodeCSP <csp>) <numVars>` (or whatever the final `encodeCSP`
   signature is) — instead of the deleted `phpEncoded`/`mcSig`/`mcLin`. Keep the
   byte-identity assertion; this is what justifies comparing the external sweep CSVs
   to the in-Lean instances. Decide here whether `Serialize.lean` survives §7's "keep
   for now" (step 4): if `validate.py` instead reads the committed `certs/*.pbp` /
   regenerates via `gen_cert.sh`, `toOPBString` may lose its last consumer and can be
   dropped.
3. **Replace `gen_mutilated_lean.py`** with a generator (or a thin wrapper over
   `scripts/gen_cert.sh`) that emits the one-line `csp_unsat_file <csp> <n>
   "certs/<name>.pbp"` theorem **plus** the `certs/<name>.pbp` file, against
   `isSatisfiableInt` and the `Int` nomenclature. The same wrapper then authors any
   new larger checkpoint (§6.5: wider ripple-carry, larger Paley — probe UNSAT with
   RoundingSat first).
4. **Re-confirm `pbgen.py` ↔ `encodeCSP` identity** via the ported `validate.py`
   ("ALL IDENTICAL"); if it diverges, regenerate `results/scaling*.csv` and refresh
   the `cert (chars)` / size columns and the in-Lean checkpoint table in SCALING.md so
   the external and in-Lean numbers stay comparable.
5. **Refresh `docs/SCALING.md`** prose for the generic pipeline: the §5 in-Lean
   checkpoint table and the §7 "what grows in-Lean is the bridge proof" note both
   describe the old per-family bridges and must be restated for the single generic
   spine. The §2–§4 separation results (PB cert size vs. DRAT) are about the
   *encoding and solvers*, not the Lean spine, so they stand — only re-run the sweep
   if step 4 shows the OPB changed.

Validation when done: `uv run python scripts/scaling/validate.py` reports ALL
IDENTICAL; `lean_timing.py` runs clean against the `Problems/` modules; and a fresh
checkpoint authored by the new generator builds via `lake build` with an axiom-clean
`#print axioms`.
