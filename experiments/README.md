# Experiments

Two reproducible studies backing the paper's experimental section. Each has **one entry-point
script**, a `results/` folder (committed data) and an `artifacts/` folder (generated files,
kept local — gitignored).

| Experiment | One-line command | What it shows |
|---|---|---|
| **Scaling** (PB vs DRAT) | `uv run python experiments/run_scaling.py` | verified cutting-planes (PB) certificates stay small where the resolution (DRAT) proof blows up (pigeonhole, mutilated chessboard); odd-cycle is the both-linear control |
| **SBC** (cost vs benefit) | `uv run python experiments/run_sbc.py` | per family, the wall-clock speedup from a *verified* symmetry-breaking constraint, plus our pipeline's own in-Lean PBLean checking cost |

Run a subset of families by naming them, e.g. `uv run python experiments/run_sbc.py php oddcycle`.

**Smoke test** — add `--smoke` to run only the **2 smallest instances per family**, to check the
whole pipeline works before committing to a full run:

```
uv run python experiments/run_sbc.py --smoke        # a few minutes
uv run python experiments/run_scaling.py --smoke
```

Smoke output is written to separate `*.smoke.*` files (gitignored) so it never pollutes the
committed results.

## Layout

```
experiments/
  run_scaling.py   run_sbc.py      # entry points
  lib/                             # shared + per-experiment helpers
  scaling/{results,artifacts}/
  sbc/{results,artifacts}/
```

`lib/` holds the machinery: `harness.py` (roundingsat + veripb runners, median-of-3 timing),
`lean_dump.py` (dump the canonical OPB from Lean), `lean_recheck.py` (`check_file_runtime` — time
the compiled `checkProofBool` on a cert read at runtime, i.e. exactly what `Lean.ofReduceBool`
reduces), `families.py` (SBC family/instance config), `pbgen.py`/`validate.py` (standalone OPB+CNF
generators and the generator-vs-Lean equality check), the sweep/aggregation/plot steps
(`scaling_sweep.py`, `scaling_lean.py`, `sbc_sweep.py`, `aggregate.py`, `scaling_plot.py`,
`check_largest.py`), and `paper_table.py` (regenerates the paper's `tab:sbc` from the CSVs).

## Results vs artifacts

- **`results/` is committed** — the CSVs and figures that feed the paper.
  - Scaling: `scaling.csv` (+ per-family), `scaling_lean.csv` (in-Lean tier), and the paper's
    per-problem proof-length figures `scaling_<fam>.png` (+ combined `scaling_all.png`, and
    `scaling_<fam>.dat` for pgfplots).
  - SBC: `sbc_scaling.csv` (per-instance solving), **`sbc_table.csv`** (wall and deterministic
    speedup — geomean and at the largest solved instance), and `check_largest.csv` (PBLean's
    checker runtime on the largest certificate per family/regime). The SBC experiment produces
    **no figures**.
- **`artifacts/` is gitignored** — every file the run generates (`.opb`, `.cnf`, `.pbp` certs
  up to 100s of MB, `.drat`) stays local. Re-running regenerates them.

## Requirements

- `lake` (Lean toolchain per `lean-toolchain`); build the project first (`lake build`).
- `roundingsat` (from `$ROUNDINGSAT`, else PATH) and `veripb` for the PB pipeline.
- `cadical` + `drat-trim` for the DRAT side of the scaling study (missing tools degrade
  gracefully to `TOOL-MISSING`).

## Notes

- **Full SBC run** takes roughly 1–2 h: some w/o-SBC instances (schur `c4n45`, vdW `W(4,3)`) hit
  the 600 s timeout by design (`censored=1` in `sbc_table.csv`, speedups are lower bounds), and the
  `check_largest` step regenerates the largest certificate per family — a few of which are 100s of
  MB (Clique K15 w/o SBC ≈ 391 MB).
- **Checking cost** (`check_largest.csv`) is PBLean's *compiled* `checkProofBool` runtime on the
  largest certificate each regime produces — the exact function `Lean.ofReduceBool` reduces.
  `check_largest.py` runs a native harness, the `checkbench` executable (`lakefile.lean` /
  `lib/CheckBench.lean`, a Mathlib-free exe importing only veripb), and `lake build`s it on demand.
  Measuring via a compiled exe (not `#eval`, which interprets and is ~10× slower) is essential:
  natively even a 391 MB certificate checks in ~3 min, and the SBC shrinks the certificate — hence
  its checking cost — as much as it shrinks the search.
- The *scaling* Lean tier still emits gitignored `CSP/L2S/Backends/PB/Bench/Scaling*Bench.lean`
  modules, because `lake build` only kernel-checks modules under `CSP/`. The *SBC* study avoids
  any source-tree writes by timing the checker via `lake env lean` on throwaway `/tmp` files.
