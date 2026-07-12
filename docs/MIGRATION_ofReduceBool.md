# Migration: discharge committed PB UNSAT theorems via `Lean.ofReduceBool`, not `native_decide`

**Status:** planned. **Audience:** the Claude agent doing the migration in the LeanCSP repo (`~/projects/leancsp`).
**Toolchain:** `leanprover/lean4:v4.30.0`. **Upstream PBLean:** vendored `veripb` v0.3.0 at `.lake/packages/veripb/`.

## Goal in one line

Switch every committed pseudo-Boolean UNSAT theorem so that its reflection step is discharged by a
**hand-built `Lean.ofReduceBool` proof term** (PBLean's own `veripb_reflect` style) instead of the
**`native_decide` tactic**, so that `#print axioms` on each theorem is exactly

```
propext, Classical.choice, Quot.sound, Lean.ofReduceBool
```

## Why (rationale)

1. **Match what upstream PBLean does and recommends.** PBLean's scalable path is reflection (its
   explicit kernel-proof-term mode, `fromVeriPBDirect`, does not scale and does not even support all
   rules such as `red`). Within reflection, *every* committed PBLean application theorem
   (`IndependentSet`, `Schur`, `Langford`, `VanDerWaerden`, `Ramsey`, `EquitableColoring`,
   `BinPacking`) is discharged by a command that constructs the `Lean.ofReduceBool` term directly
   (see `.lake/packages/veripb/VeriPB/Tactic/Sat/Reflect.lean`, `veripb_reflect`, the
   `Lean.ofReduceBool` application near line 2443, comment "Native evaluation via ofReduceBool (like
   native_decide)"). PBLean does **not** use the `native_decide` tactic for these.

2. **A single, stable, nameable axiom.** Since Lean 4.29 (PR #12217), the `native_decide` tactic emits
   a **fresh per-theorem** axiom named like `‹thm›._native.native_decide.ax_1_1` instead of the stable
   `Lean.ofReduceBool`. Hand-building the `ofReduceBool` term keeps one fixed axiom across all
   theorems. This lets the paper state the trusted base precisely ("... adds only `Lean.ofReduceBool`
   ...") and enables a policy check like "allow only `propext, Classical.choice, Quot.sound,
   Lean.ofReduceBool`."

3. **No downside on trust or speed.** Both routes admit the compiled checker's result and put the
   Lean compiler in the TCB, exactly like `bv_decide`; the choice is bookkeeping, not soundness. The
   expensive work (native evaluation of `checkProofBoolFast` on the certificate) is identical, so
   verification time is unchanged to within noise. (The only philosophical counterpoint: Lean 4.29's
   per-theorem axioms are designed for finer auditability. We deliberately prefer PBLean-alignment and
   a nameable axiom.)

## Current state (what to change)

- The committed UNSAT theorems are produced by the **`csp_unsat_file`** macro in
  `CSP/L2S/Backends/PB/GenericEncode.lean` (around line 3082). Its discharge is:
  ```lean
  VeriPB.Reflect.checkProof_sound _ $numVars (include_str $path) (by native_decide)
  ```
  `by native_decide` is what produces the fresh `._native.native_decide.ax` axiom. This macro has
  ~62 call sites (every `CSP/L2S/Backends/PB/Problems/*.lean` theorem, e.g. `Pigeonhole`,
  `GraphColoring`, `SchurVP`).

- The **template already exists**: `registerFormulaUnsat` in
  `CSP/L2S/Backends/PB/Tactic.lean` (used by the `csp_reflect_unsat` / `csp_decide` commands, itself
  "Adapted from PBLean's `independent_set_reflect`"). It builds the `ofReduceBool` term correctly:
  ```lean
  -- aux : Bool := checkProofBool cs numVars proofStr   (addAndCompile, native)
  let rflPrf  := @Eq.refl Bool (Lean.reduceBool auxConst)
  let hEqTrue := Lean.ofReduceBool auxConst Bool.true rflPrf     -- ← the stable axiom
  let unsatProof := VeriPB.Reflect.checkProof_sound cs numVars proofStr hEqTrue
  -- : VeriPB.Reflect.formulaUnsat cs
  ```

So this is not new machinery — it is routing the many `csp_unsat_file` theorems through the discharge
that `registerFormulaUnsat` / `csp_reflect_unsat` already uses.

## How (recommended change)

Make the `csp_unsat_file` path build the `ofReduceBool` term instead of calling `by native_decide`.
Two options; prefer **A**.

**Option A (single high-leverage change):** change `csp_unsat_file` itself so all ~62 call sites
switch at once.
- Wrinkle: `csp_unsat_file` is currently a **term-level macro** using `include_str` (splices the
  certificate at parse time). The `ofReduceBool` construction needs an **`Expr`-level** step
  (`addAndCompile` a fresh `Bool` aux def, then apply the axiom), which cannot be done inside a plain
  term macro. So convert it to a small **command** (or a term elaborator) that:
  1. elaborates `cs : Array Sat.PB.Constr` and `numVars : Nat`,
  2. reads the certificate string (keep `include_str` semantics by resolving the path relative to the
     module, or switch to `IO.FS.readFile` as `csp_reflect_unsat` does),
  3. calls the existing `registerFormulaUnsat` (or inlines its body).
- Net effect: the 62 `Problems/*.lean` theorems recompile unchanged in source but now carry
  `Lean.ofReduceBool`.

**Option B (mechanical, more churn):** leave `csp_unsat_file` as-is but replace each committed
`Problems/*.lean` theorem's use with the existing `csp_reflect_unsat` command. More edits, no new
elaborator, but 62 call-site rewrites. Only do this if converting the macro proves awkward.

Do **not** touch:
- the **SAT-witness** path (`csp_sat_file` / `Witness.lean`): it uses kernel `decide` and is already
  axiom-clean; leave it.
- the explicit kernel-proof-term mode: out of scope (does not scale to our ~100 MB certificates).
- the 3 demo files already using `csp_reflect_unsat` (`Backends/PB/Demo*.lean`): already correct.

## Verification (must pass before considering it done)

1. Pick 2-3 committed theorems across families, e.g. `PB.Pigeonhole` PHP UNSAT,
   `PB.GraphColoring` UNSAT, and `EndToEnd.SchurCertify.schur_3_ub`. For each:
   ```lean
   #print axioms <theoremName>
   ```
   Expected: `propext, Classical.choice, Quot.sound, Lean.ofReduceBool` — and **no**
   `‹thm›._native.native_decide.ax…`, **no** `sorryAx`.
2. `lake build` the affected modules cleanly. Spot-check that build/verification time on one large
   instance (a Schur VP certificate) is unchanged vs. before (expected: within noise).
3. Update stale prose that names the old axiom:
   - `Backends/PB/Problems/Pigeonhole.lean` and `Problems/GraphColoring.lean` docstrings (they say
     "the one `native_decide` axiom"),
   - `README.md` / `docs/ADDING_UNSAT_INSTANCES.md` wherever the fresh
     `._native.native_decide.ax_1_1` axiom name is documented as the footprint,
   - `Backends/PB/Tactic.lean` docstrings that describe the discharge (they already mention
     `Lean.ofReduceBool`; make sure they no longer imply `csp_unsat_file` uses `native_decide`).

## Paper coupling

The AAAI paper (`sec:cert`, trust-base paragraph) now states each certified theorem "adds to Lean's
standard axioms only `Lean.ofReduceBool`." That sentence is **only accurate after this migration**. A
`%TODO(depends on migration)` comment marks it in `paper.tex`; remove that comment once `#print
axioms` confirms `Lean.ofReduceBool` on the committed theorems.
