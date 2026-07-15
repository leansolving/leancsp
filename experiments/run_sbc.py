#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import sbc_sweep       # noqa: E402
import aggregate       # noqa: E402


def main():
    argv = sys.argv[1:]
    flags = {a for a in argv if a.startswith("-")}
    fams = [a for a in argv if not a.startswith("-")]
    smoke = "--smoke" in flags
    smoke_arg = ["--smoke"] if smoke else []

    # The sweep measures EVERYTHING per instance / per regime: roundingsat solve, native
    # checkProofBool runtime, and the full in-Lean `lake build` pipeline cost.
    print("== [1/2] SBC sweep (roundingsat + native check + in-Lean pipeline, per instance) ==", flush=True)
    sys.argv = ["sbc_sweep", *fams, *smoke_arg]
    sbc_sweep.main()

    print("\n== [2/2] aggregate -> sbc_table.csv (speedups + checking cost at largest instance) ==", flush=True)
    sys.argv = ["aggregate", *smoke_arg]
    aggregate.main()

    tag = " (smoke -> *.smoke.csv)" if smoke else ""
    print(f"\nDone{tag}. Results in experiments/sbc/results/; regenerate the table with paper_table.py.", flush=True)


if __name__ == "__main__":
    main()
