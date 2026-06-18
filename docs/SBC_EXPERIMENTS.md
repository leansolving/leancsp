# SBC scaling experiments (v3)

Measures the effect of a **symmetry-breaking constraint (SBC)** on the verified
pseudo-Boolean UNSAT pipeline, across classical UNSAT families. Each family is run in two
regimes — **`none`** (baseline, no SBC) and the **one SBC matched to its symmetry** — and every
instance is solved by RoundingSat, certified by VeriPB, and the certificate is kernel-checked in
Lean (`native_decide`). All SBCs used are **Lean-verified sound**, so each measured point is a
genuine `¬ csp.isSatisfiableInt` for the *original* problem.

Pipeline: `IntCSP --encodeCSP--> OPB --roundingsat--> proof log --veripb--> cert --csp_unsat_file + native_decide--> ¬ isSatisfiableInt`.
Harness: [`scripts/sbc_scaling/`](../scripts/sbc_scaling/); data → `results/sbc_v3/`.

## Families, instance sizes, and SBCs

### Value-symmetric — SBC: value precedence (Law–Lee staircase `xⱼ ≤ j`)

| Family | Instances | SBC |
|---|---|---|
| **clique** `Kₙ` / (n−1) colours | K3 … K15 | value precedence (n−1 colours) |
| **Schur** `S(c)`, critical `n = S(c)+1` | c=2: n∈{5,6,7}; c=3: n∈{14,15}; c=4: n=45 | value precedence (c colours) |
| **Van der Waerden** `W(r,3)` | (r,n) ∈ {(2,9),(2,10),(2,11),(3,27),(3,28),(4,76)} | value precedence (r colours) |
| **pigeonhole** PHP(h+1,h) | h=2 … 12 | value precedence (h colours) |
| **clique-colouring** Mycielskian `Mⱼ` (χ=j+2) / (j+1) colours | M2, M3, M4 | value precedence (j+1 colours) |

### Binary value-symmetric (2 colours) — value precedence degenerates to `x₀ = 0`

| Family | Instances | SBC |
|---|---|---|
| **Ramsey** diagonal `R(3,3)` | n ∈ {6,7,8,9,10} | value precedence (≡ x₀=0) |
| **odd cycle** `C₂ₘ₊₁` 2-colour | C5, C7, … , C51 | value precedence (≡ x₀=0) |

### Variable-symmetric — SBC: a Lean-verified variable symmetry breaker

| Family | Instances | SBC |
|---|---|---|
| **mutilated chessboard** `2k×2k` | 4×4, 6×6, 8×8, 10×10, 12×12 | diagonal reflection `(r,c)↦(c,r)` |
| **perfect matching** `K₂ₘ₊₁` | K5, K7, K9, K11, K13, K15, K17, K19 | vertex transposition (swap 0↔1) |
| **Langford** `L(2,n)` (UNSAT, n≡1,2 mod 4) | n ∈ {2,5,6,9,10} | sequence reversal (`x₀ ≤ n−1`) |

Each family auto-stops at the RoundingSat timeout or the `native_decide` certificate-size cap
(harder instances would only time out too).

## How the sizes were chosen (two family classes)

A size probe (RoundingSat `none` regime, the hard baseline) shows families split in two:

* **Search-hard — solving time grows into seconds/minutes.** clique (K12 2.1s → K15 196s),
  clique-colouring (M4 63s), perfect matching (K17 1.5s → K19 14.2s; K21+ time out), Langford
  (n9 2.7s, n10 4.5s; n13+ time out), and the **high-colour** instances of Schur/VdW. **For
  Schur and VdW the hard axis is the *number of colours* at the critical n, not n itself** —
  pushing n past the threshold adds constraints and makes the instance *easier*. The hard points
  are **Schur c=4 (n=45)** and **VdW r=4 (n=76)**: `none` times out, the SBC solves in tens of
  seconds. The ladders above are tuned to this — they end just before the timeout cliff.
* **CP-easy — solving time stays in the milliseconds at every size** (1–2 conflicts): pigeonhole,
  mutilated chessboard, Ramsey, odd cycle. No size increase moves them (intrinsic to cutting
  planes), so their meaningful metric is **certificate size / conflicts**, not wall-clock.

Note: the search-hard instances produce large certificates that exceed the `native_decide` cap,
so they are measured for solving time **externally** but fall outside the Lean-verified subset.

## Results

<!-- fill in when the run completes: results/sbc_v3/sbc_scaling.csv (per-instance metrics),
     sbc_scaling_lean.csv (per-family native_decide build), sbc_speedup.csv, sbc_<family>.png -->

_(to be filled in)_

## Reproduce

```bash
uv run python scripts/sbc_scaling/run_sbc_scaling.py     # sweep → results/sbc_v3/ + V3*Bench.lean
uv run python scripts/sbc_scaling/plot.py sbc_v3         # figures + speedup table
```
