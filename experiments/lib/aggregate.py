#!/usr/bin/env python3
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
    "check_none_hi", "check_sbc_hi",                            # native checkProofBool runtime (ns) at largest
    "check_none_status", "check_sbc_status",                    # OK / TIMEOUT / FALSE (cert REJECTED) of the check
    "pipe_none_hi", "pipe_sbc_hi",                              # in-Lean pipeline cost (s) at largest
    "pipe_none_status", "pipe_sbc_status",                      # OK / TIMEOUT / BUILD-FAIL of the in-Lean build
    "n_pairs", "censored",
]
# Checking costs are measured per instance during the sweep (sbc_sweep.py); here we surface the
# value at the LARGEST instance per family, matching the solver columns.


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


def _p(v):
    """Store a value at full precision (exact integer, else many sig figs) so the true speedup
    survives; display rounding happens in latex_table.py."""
    if v is None:
        return ""
    if v == int(v):
        return str(int(v))
    return f"{v:.12g}"


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
        # `sizes` = instances where at least one regime solved; the largest instance that timed out
        # in BOTH regimes (e.g. vdW W(4,3)) is dropped, so the "largest" columns are never all-t/o.
        sizes = sorted({int(r["size_param"]) for r in rs
                        if r.get("size_param") and r["roundingsat_status"] == "UNSAT"})

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

        # value at the largest instance of the range; blank if that regime was censored (timed
        # out) there, so the ratio reads as a lower bound.
        hi = sizes[-1] if sizes else None

        def at_hi(regime, col):
            for r in rs:
                if (r["regime"] == regime and r["roundingsat_status"] == "UNSAT"
                        and r.get("size_param") and int(r["size_param"]) == hi):
                    return _f(r.get(col))
            return None

        def at_hi_val(regime, col):          # raw cell (not parsed) at the largest instance
            for r in rs:
                if (r["regime"] == regime and r["roundingsat_status"] == "UNSAT"
                        and r.get("size_param") and int(r["size_param"]) == hi):
                    return r.get(col, "")
            return ""

        def hi_stats(col, floor=0.0):
            n, s = at_hi("none", col), at_hi(sbc_regime, col)
            spd = (max(n, floor) / max(s, floor)) if (n and s) else None
            return n, s, spd

        wall_none_hi, wall_sbc_hi, wall_spd_hi = hi_stats("roundingsat_time_s", WALL_FLOOR)
        det_none_hi, det_sbc_hi, det_spd_hi = hi_stats("rsat_det_time")

        # censored ⇔ the w/o-SBC regime did NOT solve at the displayed largest instance, so its
        # cell is t/o and the speedup there is a lower bound (e.g. Schur c=4, n=45).
        censored = 1 if at_hi("none", "rsat_det_time") is None else 0

        out.append({
            "family": fam, "sbc": sbc_desc,
            "size_lo": sizes[0] if sizes else "", "size_hi": sizes[-1] if sizes else "",
            "wall_none_geo": _fmt(wall_none),
            "wall_sbc_geo": _fmt(wall_sbc),
            "speedup_wall_geo": _p(wall_spd),
            "wall_none_hi": _p(wall_none_hi),
            "wall_sbc_hi": _p(wall_sbc_hi),
            "speedup_wall_hi": _p(wall_spd_hi),
            "det_none_geo": _fmt(det_none, sig=4),
            "det_sbc_geo": _fmt(det_sbc, sig=4),
            "speedup_det_geo": _p(det_spd),
            "det_none_hi": _p(det_none_hi),
            "det_sbc_hi": _p(det_sbc_hi),
            "speedup_det_hi": _p(det_spd_hi),
            "check_none_hi": at_hi_val("none", "check_ns"),
            "check_sbc_hi": at_hi_val(sbc_regime, "check_ns"),
            "check_none_status": at_hi_val("none", "check_status"),
            "check_sbc_status": at_hi_val(sbc_regime, "check_status"),
            "pipe_none_hi": at_hi_val("none", "pipeline_net_s"),
            "pipe_sbc_hi": at_hi_val(sbc_regime, "pipeline_net_s"),
            "pipe_none_status": at_hi_val("none", "pipeline_status"),
            "pipe_sbc_status": at_hi_val(sbc_regime, "pipeline_status"),
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
