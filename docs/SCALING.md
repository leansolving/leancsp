# Scaling study: verified cutting-planes vs. resolution

This document measures how the **verified pseudo-Boolean (PB) UNSAT pipeline**
(`CSP/L2S/Backends/PB/`) scales across three problem families, and contrasts it
with the **resolution (DRAT)** pipeline that a CDCL SAT solver produces.

**Headline result.** On two families that are *exponentially hard for resolution*
— the pigeonhole principle (Haken 1985) and the mutilated chessboard
(Alekhnovich 2004) — but admit *polynomial cutting-planes* refutations, the
verified-PB certificate (and its in-Lean `native_decide` recheck) grows
**polynomially**, while the resolution proof a SAT solver must emit grows
**exponentially** and walls at a hard timeout. The ripple-carry adder is included
as an *easy linear baseline*: the verified PB pipeline never hits a search wall on
it at any width tried.

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
  n=2,4; mutilated k=2). So the external certificate-size numbers are directly
  comparable to the in-Lean instances.
* The **CNF** is the natural DIMACS encoding of the *same* instance (one-hot
  pigeon/hole or domino-placement variables) — the standard resolution-hard form.
* **roundingsat** is the cutting-planes PB solver; **veripb --elaborate** turns its
  proof log into a kernel-checkable VeriPB certificate (the string the Lean theorem
  embeds and re-validates with `native_decide`).
* **cadical** is the CDCL SAT solver (a resolution engine); **drat-trim** checks its
  DRAT proof. cadical/kissat are *resolution* solvers, so on these families they
  must produce exponential-size proofs.

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

## 4. Ripple-carry adder, w-bit — the easy linear baseline

A correctness query for a w-bit adder, encoded with the order encoding: carry-in
`c0 = 0`, per-bit full-adder identity `a_i + b_i + c_i = s_i + 2c_{i+1}`, and a
one-sided correctness miter `Result ≥ A + B + 1` (UNSAT, since the identities force
`Result = A + B`). Everything is linear over `{0,1}` — no Big-M, no resolution
hardness — so this is the *easy* family. (No DRAT contrast: the family is not
resolution-hard, per the task scope.)

> This is a deliberately explicit, fully-linear variant for the sweep. The committed
> in-Lean theorem `ripple_carry_4bit_correct_unsat` instead folds the gate semantics
> into a single full-adder identity *inside the Lean proof* (leaving a 4-constraint
> OPB), so its OPB and this sweep's differ; both ride the same verified order encoding.

| w (bits) | PB vars | PB constr | roundingsat (s) | **PB cert (chars)** |
|--:|----:|----:|----:|----:|
| 4  | 17  | 10 | 0.037 | 263 |
| 8  | 33  | 18 | 0.036 | 348 |
| 12 | 49  | 26 | 0.036 | 429 |
| 16 | 65  | 34 | 0.037 | 506 |
| 20 | 81  | 42 | 0.039 | 578 |
| 24 | 97  | 50 | 0.066 | 48 760 |
| 28 | 113 | 58 | 0.080 | 57 634 |
| 32 | 129 | 66 | 4.32  | 2 674 971 |

**Finding.** Through **w = 20** the certificate grows **strictly linearly**
(263 → 578 chars, +18 chars per 4 bits) with roundingsat flat at **~0.037 s** — the
clean linear baseline. From **w ≥ 24** the `2^w` binary output weights leave
roundingsat's small-coefficient regime and the cutting-planes *arithmetic* in the
proof balloons (48 KB → 2.7 MB), but this is a **coefficient-size artifact, not an
exponential search wall**: roundingsat still solves w = 32 in 4.3 s and veripb still
verifies. Unlike pigeonhole and the mutilated board, the verified PB pipeline
**never fails** on the adder at any width tried.

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
| `mutilated_chessboard_unsat` (4×4) | `MutilatedChessboard.lean` | 456 | < 0.01 | — |
| `mutilated_chessboard_6_unsat` (6×6) | `MutilatedChessboard6.lean` | 937 | 0.13 | 29.4 |

**New theorems committed by this study:** `php_7_6_unsat`, `php_9_8_unsat`
(`Pigeonhole.lean`), `mutilated_chessboard_6_unsat` (`MutilatedChessboard6.lean`).

**Finding.** The `native_decide` recheck of the certificate is **negligible**
(< 0.15 s) — the certificates are tiny (≤ 7-line kernel proofs), so re-checking a
committed theorem from Lean alone is essentially free. The in-Lean cost that does
grow with instance size is the **soundness-bridge proof** (e.g. the 6×6 board's
34-cell × 2-half `mc_hlin`, which dominates its 29 s module build), not the
certificate recheck. This is a property of the current generic spines rather than
of the verified pipeline itself.

---

## 6. Reproducing

```bash
# 1. Confirm the standalone OPB generator matches the verified Lean encoder
uv run python scripts/scaling/validate.py            # ALL IDENTICAL

# 2. Run the external sweeps (writes results/scaling_<family>.csv + scaling.csv)
uv run python scripts/scaling/run_scaling.py php
uv run python scripts/scaling/run_scaling.py mutilated
uv run python scripts/scaling/run_scaling.py ripple
#    (or `run_scaling.py` for all three; `run_scaling.py merge` to recombine)

# 3. Measure the in-Lean checkpoint costs (writes results/scaling_lean.csv)
uv run python scripts/scaling/lean_timing.py
```

`scripts/scaling/gen_mutilated_lean.py` regenerates the `MutilatedChessboard<2k>.lean`
instance module for any `k` (used to author the 6×6 checkpoint).

---

## 7. Notes and future work

* **The separation is the cutting-planes vs. resolution gap, made verifiable.**
  Pigeonhole and the mutilated chessboard are textbook examples where cutting
  planes is exponentially stronger than resolution; this study shows the *verified*
  cutting-planes certificate realises that gap end-to-end, with a kernel-checked
  Lean theorem at the polynomial end and a SAT solver hitting an exponential wall at
  the other.
* **Coefficient size, not search, bounds the adder.** The ripple w ≥ 24 cert growth
  is roundingsat's large-coefficient arithmetic, not search hardness; a
  non-binary-weighted miter would keep the certificate linear throughout.
* **Deferred: ripple in-Lean 8-/16-bit checkpoints.** The committed 4-bit ripple
  theorem (`RippleCarry.lean`) verifies the *gate-level* circuit (XOR/AND/OR gate
  constraints per bit) and folds the gates into the Lean proof via the full-adder
  identity. A *faithful* wider checkpoint needs gate-level corpus models at those
  widths — only the hard-coded 4-bit `ripple_carry_adder_4bit` exists — plus a
  generalisation of the bespoke ~240-line telescoping proof. The cheap alternative
  — committing the §4 *linear-spec* variant (which asserts the full-adder identity
  directly as a `linear_eq` constraint rather than deriving it from gates) — is
  **deliberately not taken**: that theorem would be near-vacuous (it certifies only
  that a system of linear equations plus a contradictory inequality is infeasible,
  verifying *no circuit*), so committing it as "ripple-carry verification" would
  misrepresent it. The faithful gate-level generalisation is the right follow-up;
  meanwhile the external linear-baseline sweep above already characterises the
  scaling, and the native_decide recheck cost is family-independent (it depends on
  certificate size, measured in §5 to be negligible).
