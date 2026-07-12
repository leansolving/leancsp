#!/usr/bin/env python3
"""Entry point for the DRAT-vs-PB scaling experiment (one command runs the whole study).

  [1] validate  — assert the standalone OPB generator is byte-identical to the in-Lean encoder,
  [2] sweep     — external sweep: PB (roundingsat + veripb) vs DRAT (cadical + drat-trim),
  [3] lean tier — kernel-check the PB certificates in Lean, timing encode vs check per instance.

Committed data lands in experiments/scaling/results/; all generated scratch (opb/cnf/pbp/drat)
stays local under experiments/scaling/artifacts/.

Usage:
  uv run python experiments/run_scaling.py                  # full study, all families
  uv run python experiments/run_scaling.py php oddcycle     # a subset of families
  uv run python experiments/run_scaling.py --no-lean        # skip the (slow) Lean tier
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import validate          # noqa: E402
import scaling_sweep     # noqa: E402
import scaling_lean      # noqa: E402


def main():
    argv = sys.argv[1:]
    flags = {a for a in argv if a.startswith("-")}
    fams = [a for a in argv if not a.startswith("-")] or ["php", "mutilated", "oddcycle"]
    smoke = "--smoke" in flags          # only the 2 smallest sizes per family (quick check)
    smoke_arg = ["--smoke"] if smoke else []

    print("== [1/3] validate: OPB generator == in-Lean encoder ==", flush=True)
    if validate.main() != 0:
        sys.exit("validation failed — aborting")

    print("\n== [2/3] external DRAT-vs-PB sweep ==", flush=True)
    sys.argv = ["scaling_sweep", *fams, *smoke_arg]
    scaling_sweep.main()

    if "--no-lean" not in flags:
        lean_fams = [f for f in fams if f in scaling_lean.FAMILIES]
        if lean_fams:
            print("\n== [3/3] Lean-verified tier (kernel-check certs) ==", flush=True)
            sys.argv = ["scaling_lean", *lean_fams, *smoke_arg]
            scaling_lean.main()

    tag = " (smoke → *.smoke.csv)" if smoke else ""
    print(f"\nDone{tag}. Results in experiments/scaling/results/.", flush=True)


if __name__ == "__main__":
    main()
