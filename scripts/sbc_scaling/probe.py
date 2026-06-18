#!/usr/bin/env python3
"""Quick roundingsat probe to estimate per-family ceilings before the full sweep."""
from __future__ import annotations

import sys
import tempfile
from pathlib import Path

import families as F
import harness as H
import lean_dump


def probe(fam, sizes, regimes=("none", "vp")):
    cfg = F.FAMILIES[fam]
    print(f"\n=== {fam} ({cfg['note']}) ===")
    print(f"{'size':>5} {'regime':>6} {'vars':>6} {'cons':>7} {'opbKB':>7} "
          f"{'status':>9} {'detTime':>9} {'confl':>8} {'dec':>8} {'cpu_s':>9}")
    for s in sizes:
        for rg in regimes:
            expr = F.regime_expr(cfg["expr"](s), rg, cfg["colors"](s))
            try:
                nv, opb = lean_dump.dump(cfg["module"], expr)
            except Exception as e:
                print(f"{s:>5} {rg:>6}  DUMP-FAIL: {str(e)[:60]}")
                continue
            v, c = H.opb_header(opb)
            with tempfile.TemporaryDirectory() as d:
                opbp = Path(d) / "x.opb"; pbp = Path(d) / "x.pbp"
                opbp.write_text(opb)
                row, ok = H.run_roundingsat(opbp, pbp)
            print(f"{s:>5} {rg:>6} {v:>6} {c:>7} {len(opb) / 1024:>7.1f} "
                  f"{row['roundingsat_status']:>9} {row.get('rsat_det_time', ''):>9} "
                  f"{row.get('rsat_conflicts', ''):>8} {row.get('rsat_decisions', ''):>8} "
                  f"{row.get('rsat_cpu_s', ''):>9}")


PLANS = {
    "schur2": [5, 8, 11, 14, 17],
    "schur3": [14, 16, 18, 20],
    "vdw": [9, 12, 15, 18],
    "clique": [4, 5, 6, 7],
    "oddcycle": [5, 10, 15],
    "php": [2, 5, 8, 11],
    "ramsey": [6, 7],
}

if __name__ == "__main__":
    fams = sys.argv[1:] or ["schur2", "vdw", "clique", "oddcycle"]
    for fam in fams:
        probe(fam, PLANS[fam])
