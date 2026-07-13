#!/usr/bin/env python3
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "lib"))
import sbc_sweep       # noqa: E402
import aggregate       # noqa: E402
import check_largest   # noqa: E402


def main():
    argv = sys.argv[1:]
    flags = {a for a in argv if a.startswith("-")}
    fams = [a for a in argv if not a.startswith("-")]
    smoke = "--smoke" in flags
    smoke_arg = ["--smoke"] if smoke else []

    print("== [1/3] SBC sweep (dump OPB -> roundingsat -> veripb) ==", flush=True)
    sys.argv = ["sbc_sweep", *fams, *smoke_arg]
    sbc_sweep.main()

    print("\n== [2/3] aggregate -> sbc_table.csv (wall + deterministic speedup) ==", flush=True)
    sys.argv = ["aggregate", *smoke_arg]
    aggregate.main()

    if not smoke:
        print("\n== [3/3] checker runtime on the largest certificate per family ==", flush=True)
        sys.argv = ["check_largest", *fams]
        check_largest.main()

    tag = " (smoke -> *.smoke.csv)" if smoke else ""
    print(f"\nDone{tag}. Results in experiments/sbc/results/.", flush=True)


if __name__ == "__main__":
    main()
