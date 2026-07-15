#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import validate          # noqa: E402
import scaling_sweep     # noqa: E402


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

    if "--no-plot" not in flags:
        print("\n== [3/3] paper figures (proof length: VeriPB vs DRAT) ==", flush=True)
        try:
            import scaling_plot          # matplotlib only needed here
            sys.argv = ["scaling_plot", *smoke_arg]
            scaling_plot.main()
        except ImportError:
            print("  matplotlib not installed — skipping figures (data already written); "
                  "`pip install matplotlib` to enable, or pass --no-plot to silence.", flush=True)

    tag = " (smoke → *.smoke.*)" if smoke else ""
    print(f"\nDone{tag}. Results in experiments/scaling/results/.", flush=True)


if __name__ == "__main__":
    main()
