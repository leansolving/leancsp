# SBC scaling study: none vs x₀=0 vs value precedence

This study measures the effect of **symmetry-breaking constraints (SBC)** on the verified
pseudo-Boolean (PB) UNSAT pipeline. For the *same* UNSAT problems it compares three regimes:

| Regime | Constraint added | Symmetry broken |
|--------|------------------|-----------------|
| **none** | — | (full `Sₖ` colour symmetry left intact) |
| **x0** | `equals_const ⟨0,_⟩ 0` | one `Sₖ` generator (orbit shrink ×k) |
| **vp** | `value_precedence colors` | the *full* `Sₖ` (orbit → 1) |

Every measured instance×regime is a **kernel-checked Lean theorem** — the committed bench corpus
`CSP/L2S/Backends/PB/Bench/*Bench.lean` (one-line `csp_unsat_file` over a committed certificate), so
a bare `lake build` re-verifies the whole study. Nothing is measured that Lean has not verified.

## Method

For each `(family, size, regime)`:

```
IntCSP  ──encodeCSP (verified, the same encoder the theorems use)──▶  OPB
OPB     ──roundingsat──▶  proof log  ──veripb --elaborate──▶  kernel cert (committed)
cert    ──csp_unsat_file + native_decide (PBLean checker, in Lean)──▶  ¬ csp.isSatisfiableInt
```

The harness lives in [`scripts/sbc_scaling/`](../scripts/sbc_scaling/):
`lean_dump.py` (CSP term → canonical OPB), `harness.py` (roundingsat/veripb + metric parsing),
`lean_recheck.py` (in-Lean `native_decide` recheck timing), `families.py` (per-family CSP-term
builders + ladders), `run_sbc_scaling.py` (driver, auto-stops each family/regime at the roundingsat
timeout or the `native_decide` cap), `plot.py` (figures). Raw data in
[`results/sbc/`](../results/sbc/).

### Metrics

* **Search effort** — roundingsat's **deterministic time** (a machine-independent operation count)
  plus **conflicts** / **decisions**. This is the primary signal: wall-clock solve times here are
  sub-millisecond and dominated by noise, whereas the deterministic counters cleanly expose the
  exponential-vs-flat separation between regimes.
* **Certificate length** — kernel cert chars, veripb proof lines/bytes, roundingsat log lines/bytes.
* **Certificate-checking time** — veripb `--elaborate` (external) and the in-Lean **`native_decide`**
  recheck (the cost the committed theorem actually pays; minus an import baseline).
* **Encoding size** — PB variables, PB constraints, OPB bytes.

### What to expect (cutting-planes caveat)

RoundingSat reasons with **cutting planes**, which is much stronger than resolution. So the SBC
*solving-time* payoff is large only where the no-SBC problem is genuinely hard for cutting planes
**and** rich in colour symmetry:

* **Clique colouring** (`Kₙ` with `n−1` colours) — the headline: strong colour symmetry, search
  effort grows steeply without an SBC; value precedence collapses it to ~zero search. Also the place
  where `native_decide` feasibility (the binding constraint) is most extended by the SBC.
* **Van der Waerden** — a modest, real reduction.
* **Schur, odd cycles** — cutting-planes-easy already (few conflicts even with no SBC), so the
  effect is small; included as controls.
* **Pigeonhole** — cutting-planes-easy (short CP refutations); a correctness/breadth demonstrator,
  not a solving-time win.

## Results

**283 kernel-checked theorems** across 7 families (committed `Bench/` corpus). Raw data:
`results/sbc/sbc_scaling.csv` (per-instance external metrics), `results/sbc/sbc_scaling_lean.csv`
(per-family `lake build` = native_decide of all that family's theorems), `results/sbc/sbc_speedup.csv`
(deterministic-time speedup of x0 / vp over none), and `results/sbc/sbc_<family>.png`.

### Deterministic-time speedup over no SBC (the headline)

| Family (CP-hardness) | colours | x0 speedup | **vp speedup** |
|---|---|---|---|
| **clique** `Kₙ`/(n−1) (hard) | n−1 | 1.5–9× | **K7 1 711×, K8 7 279×, K10 23 728×** |
| schur3 (medium) | 3 | 3–4× | **5.5–8.3×** |
| vdw (medium) | 2 | 1.6–2.5× | 1.6–2.5× (= x0) |
| schur2 (easy) | 2 | ~9–12× | ~9–12× (= x0) |
| oddcycle (easy) | 2 | ~8× | ~8× (= x0) |
| **php** (CP-easy) | h | 0.5× | **0.1× (10× *slower*)** |

Three regimes, read off the curves (`results/sbc/sbc_<family>.png` — deterministic time, conflicts,
cert size vs size):

* **Clique colouring is the headline.** Without an SBC the search blows up exponentially
  (deterministic time 313 → 2 223 → 13 721 → 126 603 → 1 264 746 for K4…K9; conflicts 7 → 4 157).
  Fixing one colour (`x0`) only *shifts the wall ~one size* (still exponential: 2.2M det at K10).
  **Value precedence collapses it to ~linear with 0 conflicts** (det ~300 at K12) — a **~10⁴×**
  search-effort reduction, and it is the *only* regime whose certificate stays small enough to keep
  verifying in Lean past K9.
* **≥3 colours is where vp beats x0** (full `Sₖ` vs one generator): schur3 vp ~2× better than x0.
  At 2 colours the value-precedence staircase `x₁≤1` is vacuous, so vp ≡ x0 (vdw, schur2, oddcycle).
* **Honest counter-result — SBC can hurt.** Pigeonhole is *already trivial* for cutting planes
  (det ≈ 20); adding SBC facets only enlarges the formula, so vp is **~10× slower** there. This is
  the expected CP-easy behaviour and the reason the family table above labels CP-hardness.

### Certificate size and in-Lean cost

Search effort, certificate size, and `native_decide` cost move together. For clique, the `none`/`x0`
certificates grow into the hundreds of KB (hitting the 600 KB committed-corpus cap at K9/K10), while
the `vp` certificate stays ~2–6 KB across the whole ladder — so **value precedence is also what keeps
the in-Lean kernel recheck cheap and feasible at scale**. Per-family `native_decide` build times
(all theorems of a family in one process): 12–160 s, ~0.4–2.2 s/theorem (`sbc_scaling_lean.csv`).

### Harness performance note

The driver batches **per family**, not per instance: all of a family's OPBs come from one
`lake env lean` (`lean_dump.dump_batch`), and all its theorems are native_decide-checked by one
`lake build`. This is ~2 Lean-process startups per family instead of ~5 per instance — the full
283-instance sweep runs in minutes. (The leanback MCP server is the interactive equivalent: a warm
Lean worker that loads imports once.)

## Reproduce

```bash
uv run python scripts/sbc_scaling/run_sbc_scaling.py        # full sweep (regenerates Bench corpus + CSVs)
uv run python scripts/sbc_scaling/plot.py                   # figures + speedup table
lake build                                                  # re-verifies every bench theorem
```
