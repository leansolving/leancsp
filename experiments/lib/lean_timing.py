#!/usr/bin/env python3
from __future__ import annotations

import csv
import statistics
import subprocess
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
OUT = REPO / "results" / "scaling_lean.csv"
CERT_DIR = REPO / "CSP" / "L2S" / "Backends" / "PB" / "Problems" / "certs"
PROBLEMS = "CSP.L2S.Backends.PB.Problems"


def recheck_expr(csp: str, num_vars: int, cert_name: str) -> str:
    """The certificate-soundness obligation of `csp_unsat_file <csp> <nv> <cert>`,
    restated standalone (absolute include_str path, since the temp file is in /tmp)."""
    return (f"VeriPB.Reflect.formulaUnsat (((cspSig {csp}).monotonicity ++ "
            f"EncConstr.combine (encodeCSP {csp})).toArray.map PBConstr.toNatConstr) := "
            f"VeriPB.Reflect.checkProof_sound _ {num_vars} "
            f'(include_str "{CERT_DIR}/{cert_name}") (by native_decide)')


# (family, size_param, module, csp_expr, numVars, cert_name, extra_open)
# NOTE: each generated temp file imports exactly ONE Problems module — the corpus
# modules under Tests/lean/ each define `main`, so importing two Problems wrappers
# backed by different corpus files collides on `main`.
CHECKPOINTS = [
    ("php", 2, f"{PROBLEMS}.Pigeonhole", "php_3_2", 3, "php_3_2.pbp", ""),
    ("php", 4, f"{PROBLEMS}.Pigeonhole", "php_5_4", 15, "php_5_4.pbp", ""),
    ("php", 6, f"{PROBLEMS}.Pigeonhole", "php_7_6", 35, "php_7_6.pbp", ""),
    ("php", 8, f"{PROBLEMS}.Pigeonhole", "php_9_8", 63, "php_9_8.pbp", ""),
    ("mutilated", 2, f"{PROBLEMS}.MutilatedChessboard",
     "mutilatedChessboard", 20, "mutilated.pbp", "CSP.L2S.PB.MutilatedChessboard"),
    ("mutilated", 3, f"{PROBLEMS}.MutilatedChessboard6",
     "mutilatedChessboard6", 56, "mutilated6.pbp", "CSP.L2S.PB.MutilatedChessboard6"),
    ("oddcycle", 5, f"{PROBLEMS}.OddCycle", "c5_2col", 5, "c5.pbp", ""),
    ("oddcycle", 7, f"{PROBLEMS}.OddCycle", "c7_2col", 7, "c7.pbp", ""),
    ("oddcycle", 9, f"{PROBLEMS}.OddCycle", "c9_2col", 9, "c9.pbp", ""),
]

# olean / trace / hash artifacts to delete (relative to .lake/build) to force a real
# rebuild -- lake content-hashes, so `touch` alone is a no-op.
def _rmartifacts(module: str):
    rel = module.removeprefix("CSP.").replace(".", "/")  # e.g. L2S/Backends/PB/Problems/Pigeonhole
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


def native_decide_time(module, expr, extra_open, base):
    # recheck-minus-baseline using the noise-robust min estimator: this isolates
    # the native_decide reflection run (encodeCSP evaluation + certificate check)
    # from Lean startup + Mathlib-olean load (the dominant, shared cost).
    f = Path("/tmp/_lt_recheck.lean")
    f.write_text(f"import {module}\nopen CSP.L2S CSP.L2S.PB {extra_open}\n"
                 f"example : {expr}\n")
    full = wall_min(["lake", "env", "lean", str(f)])
    return max(0.0, full - base)


def module_build_time(module, repeats=2):
    # lake content-hashes, so `touch` is a no-op; delete the olean to force a rebuild.
    def one():
        _rmartifacts(module)
        return wall(["lake", "build", module], repeats=1)
    return statistics.median([one() for _ in range(repeats)])


def main():
    rows, base_cache = [], {}
    # group by module to amortize baseline + one build measurement per module
    for fam, size, module, csp, nv, cert, extra_open in CHECKPOINTS:
        if module not in base_cache:
            base_cache[module] = baseline(module)
        nd = native_decide_time(module, recheck_expr(csp, nv, cert), extra_open,
                                base_cache[module])
        rows.append({"family": fam, "size_param": size, "module": module,
                     "native_decide_time_s": f"{nd:.3f}", "module_build_time_s": ""})
        print(f"{fam} size={size}: native_decide~{nd:.3f}s (baseline {base_cache[module]:.2f}s)")
    # module build (one per distinct module), attach to that module's largest row
    seen = set()
    for fam, size, module, csp, nv, cert, extra_open in CHECKPOINTS:
        if module in seen:
            continue
        seen.add(module)
        mb = module_build_time(module)
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
