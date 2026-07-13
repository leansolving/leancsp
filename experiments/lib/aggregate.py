#!/usr/bin/env python3
"""Aggregate the per-instance SBC sweep into the geometric-mean paper table `sbc_table.csv`.

Reads experiments/sbc/results/sbc_scaling.csv and, per family, reports:

  * wall-clock solver time without / with the SBC, and their speedup — both as a geometric
    mean over the range and at the largest instance,
  * roundingsat deterministic time (machine-independent search effort), same stats,
  * our pipeline's own PBLean checking cost without / with the SBC (`check_us`, geomean), and
    the fuller reflected-term verify wall (`verify_wall_s`, geomean).

Both wall and deterministic time are recorded so either can go in the paper; `censored=1` marks
families whose w/o-SBC largest instance timed out (its speedups are lower bounds).

Geometric mean is the honest aggregate when per-instance speedups span orders of magnitude
(AAAI reviewer note). The wall speedup geomean is over sizes where BOTH regimes solved within
the 600 s timeout; a family with any timed-out w/o-SBC instance is flagged `censored=1`, so its
speedups read as lower bounds. On trivially-easy families (php, oddcycle) the wall geomean sits
near the timer's ~0.1 ms floor — `rsat_det_time` stays in the per-instance CSV as a
machine-independent cross-check.

Usage: uv run python experiments/lib/aggregate.py   (or via experiments/run_sbc.py)
"""
from __future__ import annotations

import csv
import math
import sys
from collections import defaultdict
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
RES = REPO / "experiments" / "sbc" / "results"

WALL_FLOOR = 1e-4    # roundingsat wall is printed to 4 dp; clamp so sub-0.1 ms ≠ log(0)

COLUMNS = [
    "family", "sbc", "size_lo", "size_hi",
    "wall_none_geo", "wall_sbc_geo", "speedup_wall_geo",        # wall-clock (s), geomean
    "wall_none_hi", "wall_sbc_hi", "speedup_wall_hi",           # wall-clock at the largest instance
    "det_none_geo", "det_sbc_geo", "speedup_det_geo",           # roundingsat deterministic effort
    "det_none_hi", "det_sbc_hi", "speedup_det_hi",              # deterministic at the largest instance
    "check_none_geo_us", "check_sbc_geo_us",                    # PBLean checkProofBool cost (µs)
    "verify_none_geo_s", "verify_sbc_geo_s",                    # full reflected-term verify (s)
    "n_pairs", "censored",
]


def _f(x):
    """Parse a CSV cell as a positive float, or None if empty/non-numeric/≤0."""
    try:
        v = float(x)
        return v if v > 0 else None
    except (TypeError, ValueError):
        return None


def geomean(xs, floor=0.0):
    xs = [max(x, floor) for x in xs if x is not None and x > 0]
    if not xs:
        return None
    return math.exp(sum(math.log(x) for x in xs) / len(xs))


def _fmt(v, sig=3):
    if v is None:
        return ""
    if v == 0:
        return "0"
    return f"{v:.{sig}g}"


def aggregate(rows):
    # group per family: solved rows keyed by (size, regime); the SBC regime is the non-"none" one
    fam_rows = defaultdict(list)
    for r in rows:
        fam_rows[r["family"]].append(r)

    out = []
    for fam in sorted(fam_rows):
        rs = fam_rows[fam]
        sbc_regime = next((r["regime"] for r in rs if r["regime"] != "none"), None)
        sbc_desc = next((r["sbc"] for r in rs if r["regime"] == sbc_regime), "")
        sizes = sorted({int(r["size_param"]) for r in rs if r.get("size_param")})

        # matched solved pairs (both regimes UNSAT) for a solver metric → per-regime geomean +
        # geomean of the per-instance speedup.  `floor` clamps sub-resolution values off log(0).
        def paired_geo(col, floor=0.0):
            vals = {rg: {} for rg in ("none", sbc_regime)}
            for r in rs:
                if r["roundingsat_status"] == "UNSAT" and r["regime"] in vals:
                    v = _f(r.get(col))
                    if v is not None:
                        vals[r["regime"]][int(r["size_param"])] = v
            pairs = sorted(set(vals["none"]) & set(vals[sbc_regime]))
            none_g = geomean([vals["none"][s] for s in pairs], floor)
            sbc_g = geomean([vals[sbc_regime][s] for s in pairs], floor)
            spd_g = geomean([vals["none"][s] / vals[sbc_regime][s] for s in pairs])
            return none_g, sbc_g, spd_g, len(pairs)

        wall_none, wall_sbc, wall_spd, n_pairs = paired_geo("roundingsat_time_s", WALL_FLOOR)
        det_none, det_sbc, det_spd, _ = paired_geo("rsat_det_time")

        # value at the largest instance of the range (per the paper's "largest" columns); blank if
        # that regime was censored (timed out) there, so the ratio reads as a lower bound.
        hi = sizes[-1] if sizes else None

        def at_hi(regime, col):
            for r in rs:
                if (r["regime"] == regime and r["roundingsat_status"] == "UNSAT"
                        and r.get("size_param") and int(r["size_param"]) == hi):
                    return _f(r.get(col))
            return None

        def hi_stats(col, floor=0.0):
            n, s = at_hi("none", col), at_hi(sbc_regime, col)
            spd = (max(n, floor) / max(s, floor)) if (n and s) else None
            return n, s, spd

        wall_none_hi, wall_sbc_hi, wall_spd_hi = hi_stats("roundingsat_time_s", WALL_FLOOR)
        det_none_hi, det_sbc_hi, det_spd_hi = hi_stats("rsat_det_time")

        # pipeline cost geomeans: over all checked rows of each regime (cost is per instance)
        def cost(regime, col):
            return geomean([_f(r.get(col)) for r in rs
                            if r["regime"] == regime and r["roundingsat_status"] == "UNSAT"])

        censored = 1 if any(r["regime"] == "none" and r["roundingsat_status"] == "TIMEOUT"
                            for r in rs) else 0

        out.append({
            "family": fam, "sbc": sbc_desc,
            "size_lo": sizes[0] if sizes else "", "size_hi": sizes[-1] if sizes else "",
            "wall_none_geo": _fmt(wall_none),
            "wall_sbc_geo": _fmt(wall_sbc),
            "speedup_wall_geo": _fmt(wall_spd),
            "wall_none_hi": _fmt(wall_none_hi),
            "wall_sbc_hi": _fmt(wall_sbc_hi),
            "speedup_wall_hi": _fmt(wall_spd_hi),
            "det_none_geo": _fmt(det_none, sig=4),
            "det_sbc_geo": _fmt(det_sbc, sig=4),
            "speedup_det_geo": _fmt(det_spd),
            "det_none_hi": _fmt(det_none_hi, sig=4),
            "det_sbc_hi": _fmt(det_sbc_hi, sig=4),
            "speedup_det_hi": _fmt(det_spd_hi),
            "check_none_geo_us": _fmt(cost("none", "check_us"), sig=4),
            "check_sbc_geo_us": _fmt(cost(sbc_regime, "check_us"), sig=4),
            "verify_none_geo_s": _fmt(cost("none", "verify_wall_s")),
            "verify_sbc_geo_s": _fmt(cost(sbc_regime, "verify_wall_s")),
            "n_pairs": n_pairs, "censored": censored,
        })
    return out


def main():
    suffix = ".smoke" if "--smoke" in sys.argv else ""
    src = RES / f"sbc_scaling{suffix}.csv"
    rows = list(csv.DictReader(open(src)))
    table = aggregate(rows)
    out = RES / f"sbc_table{suffix}.csv"
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS)
        w.writeheader()
        w.writerows(table)
    print(f"wrote {out}\n")
    # echo a readable preview
    widths = {c: max(len(c), *(len(str(r[c])) for r in table)) for c in COLUMNS} if table else {}
    print("  ".join(c.ljust(widths[c]) for c in COLUMNS))
    for r in table:
        print("  ".join(str(r[c]).ljust(widths[c]) for c in COLUMNS))


if __name__ == "__main__":
    main()
