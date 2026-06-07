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

* The **OPB** is the order encoding produced by the verified in-Lean encoder.
  `scripts/scaling/pbgen.py` regenerates it standalone for the sweep; its output
  is **byte-for-byte identical** to what the committed Lean theorems check, asserted
  by `scripts/scaling/validate.py` at every size that has an in-Lean theorem (PHP
  n=2,4; mutilated k=2; odd-cycle C₅, C₇, C₉). So the external certificate-size
  numbers are directly comparable to the in-Lean instances.
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
machine        : Apple M2 (MacBook Air), 8 cores, Darwin 25.1.0 arm64
lean-toolchain : leanprover/lean4:v4.30.0  (+ Mathlib cache via `lake exe cache get`)
roundingsat    : git 57d44ad (MIAOresearch, ~/git/roundingsat)
veripb         : 3.0.1 (3.0.1-67-gec8ebad)
cadical        : 3.0.0          kissat : 4.0.3          drat-trim : (no version flag)
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
| 2  | 3   | 2   | 0.035 | 168 | 9    | 0.003 | 29 B    | 0.029 |
| 4  | 15  | 14  | 0.036 | 221 | 45   | 0.004 | 1.8 KB  | 0.030 |
| 6  | 35  | 34  | 0.038 | 269 | 133  | 0.005 | 9.9 KB  | 0.032 |
| 8  | 63  | 62  | 0.039 | 317 | 297  | 0.014 | 85 KB   | 0.033 |
| 10 | 99  | 98  | 0.039 | 366 | 561  | 0.066 | 636 KB  | 0.071 |
| 11 | 120 | 119 | 0.039 | 403 | 738  | 0.200 | 2.4 MB  | 0.197 |
| 12 | 143 | 142 | 0.041 | 428 | 949  | 0.595 | 5.7 MB  | 0.572 |
| **13** | 168 | 167 | 0.079 | **453** | 1197 | **TIMEOUT (>600)** | — | — |
| 20 | 399 | 398 | 0.047 | 628 | — | — | — | — |

**Finding.** The verified PB certificate grows **linearly** (168 → 628 chars over
n = 2…20) and roundingsat stays **flat at ~0.04 s** throughout. The resolution DRAT
proof grows **exponentially** (≈ 3.5× per hole: 29 B → 5.7 MB over n = 2…12) and
**cadical times out at n = 13** — a > 1000× jump in solve time from n = 12 (0.6 s)
in a single step, the characteristic resolution cliff. **kissat** corroborates the
wall: it times out (180 s cap) already at n = 12 and at n = 13. The exponential
wall is a property of *resolution*, not of one solver's heuristics; the verified
cutting-planes pipeline sails past it.

---

## 3. Mutilated chessboard (2k × 2k minus two opposite corners)

One Boolean variable per domino placement, a per-cell exactly-one (`sum_eq = 1`);
the cutting-planes certificate is the colour count (≤-halves over black cells vs.
≥-halves over white cells). Exponentially hard for resolution (Alekhnovich).

| k | board | PB vars | roundingsat (s) | **PB cert (chars)** | CNF clauses | cadical (s) | **DRAT proof** | drat-trim (s) |
|--:|:--:|----:|----:|----:|----:|----:|----:|----:|
| 2 | 4×4   | 20  | 0.036 | 456  | 56   | 0.003 | 105 B   | 0.027 |
| 3 | 6×6   | 56  | 0.038 | 937  | 172  | 0.005 | 6.7 KB  | 0.027 |
| 4 | 8×8   | 108 | 0.041 | 1624 | 344  | 0.009 | 38 KB   | 0.030 |
| 5 | 10×10 | 176 | 0.047 | 2525 | 572  | 0.059 | 466 KB  | 0.070 |
| 6 | 12×12 | 260 | 0.056 | 3624 | 856  | 0.667 | 7.1 MB  | 0.636 |
| 7 | 14×14 | 360 | 0.066 | 4986 | 1196 | 14.08 | **128 MB** | 13.73 |
| 8 | 16×16 | 476 | 0.075 | 6425 | — | — | — | — |

**Finding.** Same separation. The PB certificate grows **polynomially** (456 → 6425
chars, ≈ linear in the number of cells) with roundingsat at **~0.04–0.08 s**. The
resolution DRAT proof grows **exponentially** (≈ 15× per step: 105 B → 128 MB over
k = 2…7); at k = 7 the resolution proof is **128 MB and takes 14 s** to produce and
14 s to check, versus a **5 KB** PB certificate produced in **66 ms**. cadical does
not wall by k = 7 (it is a strong solver), but the exponential trajectory is
unmistakable — at k = 8 the proof would be ≈ 2 GB.

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
| 3    | 3    | 6    | 0.037 | 224   | 6    | 0.004 | 16 B   | 0.027 |
| 5    | 5    | 10   | 0.036 | 283   | 10   | 0.003 | 24 B   | 0.027 |
| 7    | 7    | 14   | 0.036 | 347   | 14   | 0.004 | 34 B   | 0.027 |
| 9    | 9    | 18   | 0.036 | 405   | 18   | 0.003 | 42 B   | 0.026 |
| 11   | 11   | 22   | 0.034 | 471   | 22   | 0.003 | 54 B   | 0.027 |
| 51   | 51   | 102  | 0.037 | 1791  | 102  | 0.004 | 274 B  | 0.027 |
| 101  | 101  | 202  | 0.041 | 3515  | 202  | 0.004 | 550 B  | 0.027 |
| 201  | 201  | 402  | 0.042 | 7067  | 402  | 0.004 | 1.2 KB | 0.029 |
| 501  | 501  | 1002 | 0.052 | 18225 | 1002 | 0.004 | 3.1 KB | 0.028 |
| 1001 | 1001 | 2002 | 0.071 | 37477 | 2002 | 0.004 | 6.4 KB | 0.028 |

**Finding.** Both pipelines stay small and grow **linearly** in `n`. The PB
certificate is ≈ 37 chars per vertex (224 → 37 477 over n = 3…1001) with roundingsat
flat at **~0.035–0.07 s**. Crucially, the resolution DRAT proof *also* stays
linear — ≈ 6.4 bytes per vertex (16 B → 6.4 KB over the same range) — with cadical
flat at **~0.004 s** and drat-trim flat at **~0.027 s**. There is **no wall on
either side**. This is exactly what makes odd-cycle the right control: it is the
same order-encoding pipeline and the same DRAT pipeline used for pigeonhole and the
mutilated board, but here resolution does *not* blow up. So the exponential walls in
§2–§3 are a property of *resolution refuting those specific problems*, not an
artifact of the encoding, the serializer, or the measurement harness.

---

## 5. In-Lean checkpoints

Each larger instance is committed as a kernel-checked end-to-end
`¬ ....isSatisfiable` theorem (axiom-clean: `propext, Classical.choice, Quot.sound`
+ one `native_decide` certificate axiom; no `sorryAx`). Two in-Lean costs, both
measured by `scripts/scaling/lean_timing.py`:

* **native_decide recheck** — the time `native_decide` spends running PBLean's
  verified checker on the embedded certificate (recheck-file wall minus an
  import-only baseline, min of 5 to suppress noise).
* **module build** — `lake build` of the module after deleting its olean (imports
  cached); this is the elaboration cost that *includes* the certificate recheck.

| Theorem | Module | cert (chars) | native_decide (s) | module build (s) |
|---------|--------|----:|----:|----:|
| `php_3_2_unsat` … `php_9_8_unsat` (4 thms) | `Pigeonhole.lean` | 168 / 221 / 269 / 317 | < 0.01 each | 3.9 (whole module) |
| `mutilated_chessboard_6_unsat` (6×6) | `MutilatedChessboard6.lean` | 937 | 0.04 | 28.1 |
| `c5_2col_unsat` / `c7_2col_unsat` / `c9_2col_unsat` | `OddCycle.lean` | 283 / 347 / 405 | 0.02 / 0.06 / 0.05 | 4.3 (whole module) |

**New theorems committed by this study:** `php_7_6_unsat`, `php_9_8_unsat`
(`Pigeonhole.lean`), `mutilated_chessboard_6_unsat` (`MutilatedChessboard6.lean`),
and `c5_2col_unsat` / `c7_2col_unsat` / `c9_2col_unsat` (`OddCycle.lean`).

**Finding.** The `native_decide` recheck of the certificate is **negligible**
(< 0.07 s) across all families — the certificates are tiny (≤ 7-line counting
proofs for pigeonhole/mutilated; ~15-line RUP chains for odd-cycle), so re-checking a
committed theorem from Lean alone is essentially free. The in-Lean cost that grows
with instance size is the **soundness-bridge proof** (e.g. the 6×6 board's 34-cell ×
2-half `mc_hlin`, which dominates its 28 s module build), not the certificate
recheck. The odd-cycle module shares one generic proof (`cycle_2col_unsat`) across
all three sizes, so its whole-module build is only ~4 s.

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
instance module for any `k` (used to author the 6×6 checkpoint).

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
* **What grows in-Lean is the bridge proof, not the recheck.** The `native_decide`
  certificate recheck is family-independent and negligible (it depends only on
  certificate size, measured in §5 to be < 0.07 s). The cost that scales is the
  generic soundness-bridge proof for a given family — a property of the current
  spines, not of the verified pipeline itself.
