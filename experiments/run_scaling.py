#!/usr/bin/env python3
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

    print("== [1/4] validate: OPB generator == in-Lean encoder ==", flush=True)
    if validate.main() != 0:
        sys.exit("validation failed — aborting")

    print("\n== [2/4] external DRAT-vs-PB sweep ==", flush=True)
    sys.argv = ["scaling_sweep", *fams, *smoke_arg]
    scaling_sweep.main()

    if "--no-lean" not in flags:
        lean_fams = [f for f in fams if f in scaling_lean.FAMILIES]
        if lean_fams:
            print("\n== [3/4] Lean-verified tier (kernel-check certs) ==", flush=True)
            sys.argv = ["scaling_lean", *lean_fams, *smoke_arg]
            scaling_lean.main()

    if "--no-plot" not in flags:
        print("\n== [4/4] paper figures (proof length: VeriPB vs DRAT) ==", flush=True)
        import scaling_plot          # matplotlib only needed here
        sys.argv = ["scaling_plot", *smoke_arg]
        scaling_plot.main()

    tag = " (smoke → *.smoke.*)" if smoke else ""
    print(f"\nDone{tag}. Results in experiments/scaling/results/.", flush=True)


if __name__ == "__main__":
    main()
