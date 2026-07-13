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
`lean_dump.py` (dump the canonical OPB from Lean), `lean_recheck.py` (`runtime_split` — time the
compiled `checkProofBool`, i.e. exactly what `Lean.ofReduceBool` reduces), `families.py` (SBC
family/instance config), `pbgen.py`/`validate.py` (standalone OPB+CNF generators and the
generator-vs-Lean equality check), and the sweep/aggregation/plot steps
(`scaling_sweep.py`, `scaling_lean.py`, `sbc_sweep.py`, `aggregate.py`, `scaling_plot.py`).

## Results vs artifacts

- **`results/` is committed** — the CSVs and figures that feed the paper.
  - Scaling: `scaling.csv` (+ per-family), `scaling_lean.csv` (in-Lean tier), and the paper's
    per-problem proof-length figures `scaling_<fam>.png` (+ combined `scaling_all.png`, and
    `scaling_<fam>.dat` for pgfplots).
  - SBC: `sbc_scaling.csv` (per-instance) and **`sbc_table.csv`** (the paper table: wall and
    deterministic speedup — geomean and at the largest instance — plus PBLean cost, both
    regimes). The SBC experiment produces **no figures**.
- **`artifacts/` is gitignored** — every file the run generates (`.opb`, `.cnf`, `.pbp` certs,
  `.drat`) stays local. Re-running regenerates them.

## Requirements

- `lake` (Lean toolchain per `lean-toolchain`); build the project first (`lake build`).
- `roundingsat` (from `$ROUNDINGSAT`, else PATH) and `veripb` for the PB pipeline.
- `cadical` + `drat-trim` for the DRAT side of the scaling study (missing tools degrade
  gracefully to `TOOL-MISSING`).

## Notes

- **Full SBC rerun** takes roughly an hour: a few w/o-SBC instances (schur `c4n45`, vdW
  `W(4,3)`) hit the 600 s timeout by design — they are flagged `censored=1` in `sbc_table.csv`
  so their speedups read as lower bounds.
- **`check_us`** (compiled `checkProofBool` runtime) is the honest per-instance pipeline cost and
  is sub-millisecond — the point being that the verified checking step is negligible next to the
  solver. **`verify_wall_s`** additionally records the whole reflected-term
  elaborate+compile+check for the "cost to admit a certified theorem" framing.
- The *scaling* Lean tier still emits gitignored `CSP/L2S/Backends/PB/Bench/Scaling*Bench.lean`
  modules, because `lake build` only kernel-checks modules under `CSP/`. The *SBC* study avoids
  any source-tree writes by timing the checker via `lake env lean` on throwaway `/tmp` files.
