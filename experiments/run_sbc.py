#!/usr/bin/env python3
"""Entry point for the SBC (symmetry-breaking constraint) experiment (one command, whole study).

  [1] sweep     — per (family, regime): dump OPB → roundingsat → veripb, and time our pipeline's
                  own in-Lean PBLean check (check_us) + full reflected-term verify (verify_wall_s),
  [2] aggregate — geometric-mean wall speedup + pblean cost per family → sbc_table.csv,
  [3] plot      — supplementary per-family search-effort / cert-size figures.

Committed data lands in experiments/sbc/results/; generated certs stay local under
experiments/sbc/artifacts/.

Usage:
  uv run python experiments/run_sbc.py                 # full study, all families (clean CSV)
  uv run python experiments/run_sbc.py php oddcycle    # a subset (appends to the CSV)
  uv run python experiments/run_sbc.py --no-plot
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import sbc_sweep     # noqa: E402
import aggregate     # noqa: E402
# `plot` (matplotlib) is imported lazily below — the sweep/smoke run must not require it.


def main():
    argv = sys.argv[1:]
    flags = {a for a in argv if a.startswith("-")}
    fams = [a for a in argv if not a.startswith("-")]
    smoke = "--smoke" in flags          # only the 2 smallest instances per family (quick check)
    smoke_arg = ["--smoke"] if smoke else []

    print("== [1/3] SBC sweep (solve + veripb + in-Lean PBLean check) ==", flush=True)
    sys.argv = ["sbc_sweep", *fams, *smoke_arg]
    sbc_sweep.main()

    print("\n== [2/3] aggregate → sbc_table.csv (geomean wall speedup + pblean cost) ==", flush=True)
    sys.argv = ["aggregate", *smoke_arg]
    aggregate.main()

    # Figures are for the full study; skip them on a smoke run.
    if "--no-plot" not in flags and not smoke:
        print("\n== [3/3] supplementary figures ==", flush=True)
        import plot          # matplotlib only needed here
        plot.main()

    tag = " (smoke → *.smoke.csv)" if smoke else ""
    print(f"\nDone{tag}. Results in experiments/sbc/results/.", flush=True)


if __name__ == "__main__":
    main()
