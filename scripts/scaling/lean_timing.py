#!/usr/bin/env python3
"""Measure the in-Lean cost of the committed scaling checkpoints.

Two numbers per instance:
  * native_decide_time_s -- wall-time for `lake env lean` to re-elaborate the
    instance's `_formulaUnsat` theorem (which runs PBLean's verified checker via
    native_decide on the embedded certificate), minus an import-only baseline for
    the same module.  This is the "recheck the certificate from Lean alone" cost.
  * module_build_time_s   -- wall-time for `lake build <module>` after touching its
    source (imports cached): the incremental module compile, which includes the
    native_decide rechecks of every certificate in the module.

All medians of 3.  Results -> results/scaling_lean.csv.  Run from repo root with lake
available:  uv run python scripts/scaling/lean_timing.py
"""

from __future__ import annotations

import csv
import statistics
import subprocess
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
OUT = REPO / "results" / "scaling_lean.csv"

# (family, size_param, module, source_path, recheck_expr)
# recheck_expr re-states the committed `_formulaUnsat` so native_decide runs once.
CHECKPOINTS = [
    ("php", 2, "CSP.L2S.Backends.PB.Pigeonhole",
     "CSP/L2S/Backends/PB/Pigeonhole.lean",
     "VeriPB.Reflect.formulaUnsat (Pigeonhole.phpEncoded.toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 3 Pigeonhole.phpKernelProof (by native_decide)"),
    ("php", 4, "CSP.L2S.Backends.PB.Pigeonhole",
     "CSP/L2S/Backends/PB/Pigeonhole.lean",
     "VeriPB.Reflect.formulaUnsat (Pigeonhole.php5Encoded.toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 15 Pigeonhole.php5KernelProof (by native_decide)"),
    ("php", 6, "CSP.L2S.Backends.PB.Pigeonhole",
     "CSP/L2S/Backends/PB/Pigeonhole.lean",
     "VeriPB.Reflect.formulaUnsat (Pigeonhole.php7Encoded.toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 35 Pigeonhole.php7KernelProof (by native_decide)"),
    ("php", 8, "CSP.L2S.Backends.PB.Pigeonhole",
     "CSP/L2S/Backends/PB/Pigeonhole.lean",
     "VeriPB.Reflect.formulaUnsat (Pigeonhole.php9Encoded.toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 63 Pigeonhole.php9KernelProof (by native_decide)"),
    ("mutilated", 3, "CSP.L2S.Backends.PB.MutilatedChessboard6",
     "CSP/L2S/Backends/PB/MutilatedChessboard6.lean",
     "VeriPB.Reflect.formulaUnsat ((encodeLinear MutilatedChessboard6.mcSig "
     "MutilatedChessboard6.mcLin).toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 56 MutilatedChessboard6.mcKernelProof (by native_decide)"),
    ("oddcycle", 5, "CSP.L2S.Backends.PB.OddCycle",
     "CSP/L2S/Backends/PB/OddCycle.lean",
     "VeriPB.Reflect.formulaUnsat (((OddCycle.cycleSig 5).monotonicity ++ "
     "OddCycle.cycleUser 5 c5Edges).toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 5 OddCycle.c5KernelProof (by native_decide)"),
    ("oddcycle", 7, "CSP.L2S.Backends.PB.OddCycle",
     "CSP/L2S/Backends/PB/OddCycle.lean",
     "VeriPB.Reflect.formulaUnsat (((OddCycle.cycleSig 7).monotonicity ++ "
     "OddCycle.cycleUser 7 c7Edges).toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 7 OddCycle.c7KernelProof (by native_decide)"),
    ("oddcycle", 9, "CSP.L2S.Backends.PB.OddCycle",
     "CSP/L2S/Backends/PB/OddCycle.lean",
     "VeriPB.Reflect.formulaUnsat (((OddCycle.cycleSig 9).monotonicity ++ "
     "OddCycle.cycleUser 9 c9Edges).toArray.map PBConstr.toNatConstr) := "
     "VeriPB.Reflect.checkProof_sound _ 9 OddCycle.c9KernelProof (by native_decide)"),
]

# olean / trace / hash artifacts to delete (relative to .lake/build) to force a real
# rebuild -- lake content-hashes, so `touch` alone is a no-op.
def _rmartifacts(module: str):
    rel = module.removeprefix("CSP.").replace(".", "/")  # e.g. L2S/Backends/PB/Pigeonhole
    for p in [f".lake/build/lib/lean/CSP/{rel}.olean",
              f".lake/build/lib/lean/CSP/{rel}.olean.hash",
              f".lake/build/lib/lean/CSP/{rel}.trace",
              f".lake/build/lib/lean/CSP/{rel}.ilean.hash",
              f".lake/build/ir/CSP/{rel}.c.hash"]:
        (REPO / p).unlink(missing_ok=True)


def wall(cmd, repeats=3):
    ts = []
    for _ in range(repeats):
        t0 = time.monotonic()
        subprocess.run(cmd, cwd=REPO, capture_output=True)
        ts.append(time.monotonic() - t0)
    return statistics.median(ts)


def wall_min(cmd, repeats=5):
    # min over N runs: a fixed cost plus positive wall-clock noise (olean load,
    # scheduler jitter) is best estimated by the minimum, not the median.
    return min(wall(cmd, 1) for _ in range(repeats))


def baseline(module, repeats=5):
    f = Path("/tmp/_lt_baseline.lean")
    f.write_text(f"import {module}\n")
    return wall_min(["lake", "env", "lean", str(f)], repeats)


def native_decide_time(module, expr, base):
    # recheck-minus-baseline using the noise-robust min estimator: the certs are
    # tiny (<=7-line kernel proofs), so this isolates the native_decide reflection
    # run from Lean startup + Mathlib-olean load (the dominant, shared cost).
    f = Path("/tmp/_lt_recheck.lean")
    f.write_text(f"import {module}\nopen CSP.L2S.PB\nexample : {expr}\n")
    full = wall_min(["lake", "env", "lean", str(f)])
    return max(0.0, full - base)


def module_build_time(module, src, repeats=2):
    # lake content-hashes, so `touch` is a no-op; delete the olean to force a rebuild.
    def one():
        _rmartifacts(module)
        return wall(["lake", "build", module], repeats=1)
    return statistics.median([one() for _ in range(repeats)])


def main():
    rows, base_cache = [], {}
    # group by module to amortize baseline + one build measurement per module
    for fam, size, module, src, expr in CHECKPOINTS:
        if module not in base_cache:
            base_cache[module] = baseline(module)
        nd = native_decide_time(module, expr, base_cache[module])
        rows.append({"family": fam, "size_param": size, "module": module,
                     "native_decide_time_s": f"{nd:.3f}", "module_build_time_s": ""})
        print(f"{fam} size={size}: native_decide~{nd:.3f}s (baseline {base_cache[module]:.2f}s)")
    # module build (one per distinct module), attach to that module's largest row
    seen = set()
    for fam, size, module, src, expr in CHECKPOINTS:
        if module in seen:
            continue
        seen.add(module)
        mb = module_build_time(module, src)
        # attach to the last (largest) row for this module
        for r in reversed(rows):
            if r["module"] == module:
                r["module_build_time_s"] = f"{mb:.2f}"
                break
        print(f"{module}: module_build={mb:.2f}s")
    with open(OUT, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["family", "size_param", "module",
                                           "native_decide_time_s", "module_build_time_s"])
        w.writeheader()
        w.writerows(rows)
    print(f"Wrote {OUT}")


if __name__ == "__main__":
    main()
