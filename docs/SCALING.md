# Scaling study: verified cutting-planes vs. resolution

This document measures how the **verified pseudo-Boolean (PB) UNSAT pipeline**
(`CSP/L2S/Backends/PB/`) scales across three problem families, and contrasts it
with the **resolution (DRAT)** pipeline that a CDCL SAT solver produces.

**Headline result.** On two families that are *exponentially hard for resolution*
— the pigeonhole principle (Haken 1985) and the mutilated chessboard
(Alekhnovich 2004) — but admit *polynomial cutting-planes* refutations, the
verified-PB certificate (and its in-Lean `native_decide` recheck) grows
**polynomially**, while the resolution proof a SAT solver must emit grows
**exponentially** and walls at a hard timeout. The third family, **odd-cycle
2-colourability**, is the *easy non-separation baseline*: it is easy for *both*
cutting planes and resolution, so both the PB certificate and the DRAT proof grow
only **linearly** with no wall. It is the control — it shows the pigeonhole /
mutilated walls are a property of *resolution on those problems*, not an artifact
of the encoding pipeline or the harness.

All raw numbers are in [`results/scaling.csv`](../results/scaling.csv) (external
solver sweep) and [`results/scaling_lean.csv`](../results/scaling_lean.csv)
(in-Lean checkpoint costs). The harness lives in
[`scripts/scaling/`](../scripts/scaling/).

---

## 1. Method

For each instance we run two pipelines on the *same* problem:

```
PB   (cutting-planes, verified):  OPB ──roundingsat──▶ .pbp ──veripb --elaborate──▶ kernel proof
DRAT (resolution,   for contrast): CNF ──cadical (--no-binary)──▶ .drat ──drat-trim──▶ checked
```

* The **OPB** is the order encoding produced by the verified in-Lean *generic*
  encoder — `(cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)`, the
  formula the one-line `csp_unsat_file` theorems kernel-check and the dump
  `scripts/gen_cert.sh` feeds to RoundingSat. `scripts/scaling/pbgen.py`
  regenerates it standalone for the sweep; its output is **byte-for-byte
  identical** to the Lean dump, asserted by `scripts/scaling/validate.py` at every
  size that has an in-Lean theorem (PHP n=2,4,6,8; mutilated k=2,3; odd-cycle C₅,
  C₇, C₉). So the external certificate-size numbers are directly comparable to
  the in-Lean instances.
* The **CNF** is the natural DIMACS encoding of the *same* instance (one-hot
  pigeon/hole, domino-placement, or per-vertex colour variables) — the standard
  form a SAT solver consumes.
* **roundingsat** is the cutting-planes PB solver; **veripb --elaborate** turns its
  proof log into a kernel-checkable VeriPB certificate (the string the Lean theorem
  embeds and re-validates with `native_decide`).
* **cadical** is the CDCL SAT solver (a resolution engine); **drat-trim** checks its
  DRAT proof. On the two resolution-hard families cadical must produce an
  exponential-size proof; on odd-cycle (an easy 2-SAT-style instance) it stays small
  — that contrast is the point.

Wall-times are the **median of up to 3 runs** (a single run once a measurement
exceeds 90 s, to stay tractable near the wall); every solver call has a **600 s
hard timeout**. Instance sizes are deterministic (recorded once). Each pipeline
auto-stops at the first size that times out.

### Environment

```
machine        : AMD Ryzen 5 PRO 8540U (ThinkPad), 12 cores, Linux 6.14 x86_64
lean-toolchain : leanprover/lean4:v4.30.0  (+ Mathlib cache via `lake exe cache get`)
roundingsat    : git d4edbf7 (MIAOresearch, local build; `$ROUNDINGSAT`)
veripb         : 3.0.2
cadical        : 1.7.3          kissat : (not installed)          drat-trim : (no version flag)
timeout        : 600 s per solver call; median of up to 3 runs
```

Wall-times are on a normally-loaded laptop; the separation reported below is
many orders of magnitude and is insensitive to a few × of timing noise.

---

## 2. Pigeonhole `php_(n+1)_n` — the primary result

`n` holes, `n+1` pigeons, `alldifferent`. PB variables = `(n+1)(n−1)` order-encoding
thresholds; the cutting-planes certificate is essentially the same `n`-term linear
combination at every size. The CNF is the classic Haken instance.

| n (holes) | PB vars | PB constr | roundingsat (s) | **PB cert (chars)** | CNF clauses | cadical (s) | **DRAT proof** | drat-trim (s) |
|----:|----:|----:|----:|----:|----:|----:|----:|----:|
| 2  | 3   | 2   | 0.003 | 168 | 9    | 0.002 | 29 B    | 0.044 |
| 4  | 15  | 14  | 0.003 | 221 | 45   | 0.002 | 552 B   | 0.050 |
| 6  | 35  | 34  | 0.004 | 269 | 133  | 0.007 | 41 KB   | 0.054 |
| 8  | 63  | 62  | 0.003 | 317 | 297  | 0.289 | 3.9 MB  | 0.342 |
| 9  | 80  | 79  | 0.003 | 341 | 415  | 2.31  | 28 MB   | 3.06  |
| 10 | 99  | 98  | 0.004 | 366 | 561  | 20.98 | 217 MB  | 29.7  |
| 11 | 120 | 119 | 0.005 | 403 | 738  | 341.4 | **2.2 GB** | **TIMEOUT (>600)** |
| **12** | 143 | 142 | 0.004 | **428** | 949 | **TIMEOUT (>600)** | — | — |
| 20 | 399 | 398 | 0.005 | 628 | — | — | — | — |

**Finding.** The verified PB certificate grows **linearly** (168 → 628 chars over
n = 2…20) and roundingsat stays **flat at ~0.005 s** throughout. The resolution DRAT
proof grows **exponentially** (≈ 7× per hole: 29 B → 2.2 GB over n = 2…11) and
**cadical times out at n = 12** — a > 16× jump per hole in solve time near the wall
(2.3 s → 21 s → 341 s → timeout), the characteristic resolution cliff. At n = 11
even *checking* the 2.2 GB proof exceeds the 600 s timeout. The exponential
wall is a property of *resolution*, not of one solver's heuristics; the verified
cutting-planes pipeline sails past it.

---

## 3. Mutilated chessboard (2k × 2k minus two opposite corners)

One Boolean variable per domino placement, a per-cell exactly-one (`sum_eq = 1`);
the cutting-planes certificate is the colour count (≤-halves over black cells vs.
≥-halves over white cells). Exponentially hard for resolution (Alekhnovich).

| k | board | PB vars | roundingsat (s) | **PB cert (chars)** | CNF clauses | cadical (s) | **DRAT proof** | drat-trim (s) |
|--:|:--:|----:|----:|----:|----:|----:|----:|----:|
| 2 | 4×4   | 20  | 0.003 | 456  | 56   | 0.002 | 79 B    | 0.042 |
| 3 | 6×6   | 56  | 0.004 | 937  | 172  | 0.002 | 704 B   | 0.051 |
| 4 | 8×8   | 108 | 0.005 | 1624 | 344  | 0.005 | 16 KB   | 0.051 |
| 5 | 10×10 | 176 | 0.007 | 2525 | 572  | 0.058 | 479 KB  | 0.079 |
| 6 | 12×12 | 260 | 0.008 | 3624 | 856  | 0.496 | 5.0 MB  | 0.446 |
| 7 | 14×14 | 360 | 0.010 | 4986 | 1196 | 23.95 | **174 MB** | 29.3 |
| 8 | 16×16 | 476 | 0.011 | 6425 | — | — | — | — |

**Finding.** Same separation. The PB certificate grows **polynomially** (456 → 6425
chars, ≈ linear in the number of cells) with roundingsat at **~0.003–0.011 s**. The
resolution DRAT proof grows **exponentially** (≈ 18× per step: 79 B → 174 MB over
k = 2…7); at k = 7 the resolution proof is **174 MB and takes 24 s** to produce and
29 s to check, versus a **5 KB** PB certificate produced in **10 ms**. cadical does
not wall by k = 7, but the exponential trajectory is
unmistakable — at k = 8 the proof would be ≈ 3 GB.

---

## 4. Odd cycle `C_n` (n odd) — the easy non-separation baseline

The odd cycle `C_n` on vertices `0..n−1` (edges `(i, i+1)`, closing `(n−1, 0)`) is
not 2-colourable. Each vertex is a colour variable over the binary domain `{1,2}`
(one threshold bit, so the order-encoding `monotonicity` is empty); each edge `(u,v)`
is a `not_equal`, encoded into the two clauses `x_u + x_v ≥ 1` and `¬x_u + ¬x_v ≥ 1`.
Every coefficient is `0/1` — no Big-M, no place values. This family scales the
committed `k3_2col` (`C_3`, the triangle); the CNF is the canonical UNSAT
2-SAT instance (one Boolean per vertex, the same two clauses per edge).

| n (vertices) | PB vars | PB constr | roundingsat (s) | **PB cert (chars)** | CNF clauses | cadical (s) | **DRAT proof** | drat-trim (s) |
|----:|----:|----:|----:|----:|----:|----:|----:|----:|
| 3    | 3    | 6    | 0.002 | 224   | 6    | 0.002 | 15 B   | 0.051 |
| 5    | 5    | 10   | 0.003 | 283   | 10   | 0.002 | 25 B   | 0.047 |
| 7    | 7    | 14   | 0.003 | 347   | 14   | 0.003 | 33 B   | 0.043 |
| 9    | 9    | 18   | 0.002 | 405   | 18   | 0.003 | 43 B   | 0.044 |
| 11   | 11   | 22   | 0.003 | 471   | 22   | 0.002 | 53 B   | 0.044 |
| 51   | 51   | 102  | 0.004 | 1791  | 102  | 0.002 | 273 B  | 0.050 |
| 101  | 101  | 202  | 0.004 | 3515  | 202  | 0.002 | 551 B  | 0.053 |
| 201  | 201  | 402  | 0.004 | 7067  | 402  | 0.003 | 1.2 KB | 0.052 |
| 501  | 501  | 1002 | 0.007 | 18225 | 1002 | 0.003 | 3.1 KB | 0.051 |
| 1001 | 1001 | 2002 | 0.011 | 37477 | 2002 | 0.003 | 6.4 KB | 0.055 |

**Finding.** Both pipelines stay small and grow **linearly** in `n`. The PB
certificate is ≈ 37 chars per vertex (224 → 37 477 over n = 3…1001) with roundingsat
flat at **~0.002–0.011 s**. Crucially, the resolution DRAT proof *also* stays
linear — ≈ 6.4 bytes per vertex (15 B → 6.4 KB over the same range) — with cadical
flat at **~0.003 s** and drat-trim flat at **~0.05 s**. There is **no wall on
either side**. This is exactly what makes odd-cycle the right control: it is the
same order-encoding pipeline and the same DRAT pipeline used for pigeonhole and the
mutilated board, but here resolution does *not* blow up. So the exponential walls in
§2–§3 are a property of *resolution refuting those specific problems*, not an
artifact of the encoding, the serializer, or the measurement harness.

---

## 5. In-Lean checkpoints

Each larger instance is committed as a kernel-checked end-to-end
`¬ ....isSatisfiableInt` theorem (axiom-clean: `propext, Classical.choice, Quot.sound`
+ one `native_decide` certificate axiom; no `sorryAx`). Every theorem is a
**single line** through the generic pipeline —
`csp_unsat_file <csp> <numVars> "certs/<name>.pbp"` in
`CSP/L2S/Backends/PB/Problems/` — so there is no per-instance signature, encoding,
or soundness bridge; the only per-instance data are the CSP definition and the
committed certificate. Two in-Lean costs, both measured by
`scripts/scaling/lean_timing.py`:

* **native_decide recheck** — the time `native_decide` spends evaluating the
  generic encoding `encodeCSP <csp>` and running PBLean's verified checker on the
  committed certificate (recheck-file wall minus an import-only baseline, min of
  5 to suppress noise). Note this *includes* the in-kernel encoder evaluation —
  the real per-theorem cost under the generic pipeline — so these numbers are not
  comparable to the pre-generic-pipeline measurements, which rechecked pre-encoded
  constants.
* **module build** — `lake build` of the module after deleting its olean (imports
  cached); this is the elaboration cost that *includes* the certificate recheck.

| Theorem | Module | cert (chars) | native_decide (s) | module build (s) |
|---------|--------|----:|----:|----:|
| `php_3_2_unsat` … `php_9_8_unsat` (4 thms) | `Problems/Pigeonhole.lean` | 168 / 221 / 269 / 317 | < 0.01 each | 2.8 (whole module) |
| `mutilated_chessboard_unsat` (4×4) | `Problems/MutilatedChessboard.lean` | 456 | 0.01 | 3.4 |
| `mutilated_chessboard_6_unsat` (6×6) | `Problems/MutilatedChessboard6.lean` | 937 | 0.22 | 9.6 |
| `c5_2col_unsat` / `c7_2col_unsat` / `c9_2col_unsat` | `Problems/OddCycle.lean` | 283 / 347 / 405 | < 0.01 each | 2.9 (whole module) |

**Theorems committed by this study:** `php_7_6_unsat`, `php_9_8_unsat`
(`Problems/Pigeonhole.lean`), `mutilated_chessboard_6_unsat`
(`Problems/MutilatedChessboard6.lean`), and `c5_2col_unsat` / `c7_2col_unsat` /
`c9_2col_unsat` (`Problems/OddCycle.lean`).

**Finding.** The per-theorem `native_decide` cost — evaluating the generic
encoding `encodeCSP <csp>` *and* re-checking the committed certificate through
PBLean's verified checker — is **negligible to small** across all families:
< 0.01 s for every pigeonhole and odd-cycle instance, and 0.22 s for the largest
checkpoint (the 6×6 board: 56 variables, 34 exactly-one constraints). Module
builds are uniformly small (2.8–9.6 s): with the bespoke soundness bridges gone,
a module is just the CSP definition plus one-line theorems, so elaboration is
dominated by elaborating the CSP term itself, not by proof work. For comparison,
the 6×6 module took 28 s to build under the old pipeline, dominated by its
34-cell × 2-half bridge proof `mc_hlin` — that cost class no longer exists.

---

## 6. Reproducing

```bash
# 1. Confirm the standalone OPB generator matches the verified Lean encoder
uv run python scripts/scaling/validate.py            # ALL IDENTICAL

# 2. Run the external sweeps (writes results/scaling_<family>.csv + scaling.csv)
uv run python scripts/scaling/run_scaling.py php
uv run python scripts/scaling/run_scaling.py mutilated
uv run python scripts/scaling/run_scaling.py oddcycle
#    (or `run_scaling.py` for all three; `run_scaling.py merge` to recombine)

# 3. Measure the in-Lean checkpoint costs (writes results/scaling_lean.csv)
uv run python scripts/scaling/lean_timing.py
```

`scripts/scaling/gen_mutilated_lean.py` regenerates the `MutilatedChessboard<2k>.lean`
instance module for any `k` (used to author the 6×6 checkpoint). It first produces
the certificate `Problems/certs/mutilated<2k>.pbp` directly from pbgen's OPB
(RoundingSat + `veripb --elaborate`; set `ROUNDINGSAT` if the solver is not at
the default local-build path), then emits the one-line-theorem module to stdout;
`--module-only` skips the solvers and reuses the committed certificate.

---

## 7. Notes

* **The separation is the cutting-planes vs. resolution gap, made verifiable.**
  Pigeonhole and the mutilated chessboard are textbook examples where cutting
  planes is exponentially stronger than resolution; this study shows the *verified*
  cutting-planes certificate realises that gap end-to-end, with a kernel-checked
  Lean theorem at the polynomial end and a SAT solver hitting an exponential wall at
  the other.
* **Odd-cycle is the control, not a third separation.** On odd-cycle both the PB
  certificate and the resolution proof grow linearly with no wall (§4), confirmed
  in-Lean by the `c5/c7/c9_2col_unsat` checkpoints. Running it through the identical
  encoding and DRAT pipelines that pigeonhole and the mutilated board use rules out
  the alternative explanation that the §2–§3 walls come from the harness, the
  serializer, or the order encoding: they come from resolution refuting those
  counting problems.
* **The in-Lean cost is now the generic recheck, and it is small.** Under the
  generic pipeline every theorem is a single `csp_unsat_file` application; its
  `native_decide` obligation evaluates `encodeCSP` and re-checks the committed
  certificate, measured in §5 at ≤ 0.22 s even for the largest committed
  checkpoint. The per-family soundness-bridge proofs that previously dominated
  module builds are gone; what scales with instance size is the certificate size
  and the in-kernel encoder evaluation, both polynomial here.
