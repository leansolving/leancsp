#!/usr/bin/env python3
from __future__ import annotations

import csv
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

REPO = Path(__file__).resolve().parent.parent.parent
RES = REPO / "experiments" / "scaling" / "results"

# family → (panel title, x-axis label, log-x?)
PROBLEMS = {
    "php":       ("Pigeonhole", r"$n$", False),
    "mutilated": ("Mutilated chessboard", r"$k$ (board $2k\times2k$)", False),
    "oddcycle":  ("Odd cycle", r"$n$", True),
}
PB_STYLE = dict(color="#1f77b4", marker="o", markersize=4, linewidth=1.6, label="VeriPB")
DRAT_STYLE = dict(color="#d62728", marker="s", markersize=4, linewidth=1.6, label="DRAT")


def _int(x):
    try:
        v = int(x)
        return v if v > 0 else None
    except (TypeError, ValueError):
        return None


def series(rows, fam):
    """Return (pb_xy, drat_xy) as sorted lists of (size, proof_steps)."""
    pb, drat = {}, {}
    for r in rows:
        if r["family"] != fam or not r.get("size_param"):
            continue
        n = int(r["size_param"])
        if r["roundingsat_status"] == "UNSAT":
            v = _int(r.get("veripb_proof_lines"))
            if v is not None:
                pb[n] = v
        if r.get("sat_status") == "UNSAT":          # DRAT proof produced (stops at the timeout)
            v = _int(r.get("drat_lines"))
            if v is not None:
                drat[n] = v
    return sorted(pb.items()), sorted(drat.items())


def _draw(ax, fam, pb, drat):
    title, xlabel, logx = PROBLEMS[fam]
    if pb:
        ax.plot([x for x, _ in pb], [y for _, y in pb], **PB_STYLE)
    if drat:
        ax.plot([x for x, _ in drat], [y for _, y in drat], **DRAT_STYLE)
    ax.set_yscale("log")
    if logx:
        ax.set_xscale("log")
    ax.set_ylim(bottom=1)
    ax.set_title(title)
    ax.set_xlabel(xlabel)
    ax.set_ylabel("proof steps")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(loc="upper left", frameon=False)


def write_dat(fam, pb, drat, suffix):
    pbd, dd = dict(pb), dict(drat)
    sizes = sorted(set(pbd) | set(dd))
    lines = ["size pb drat"]
    for s in sizes:
        lines.append(f"{s} {pbd.get(s, 'nan')} {dd.get(s, 'nan')}")
    (RES / f"scaling_{fam}{suffix}.dat").write_text("\n".join(lines) + "\n")


def main():
    suffix = ".smoke" if "--smoke" in sys.argv else ""
    rows = list(csv.DictReader(open(RES / f"scaling{suffix}.csv")))
    fams = [f for f in PROBLEMS if any(r["family"] == f for r in rows)]

    # combined figure, one panel per family
    fig, axs = plt.subplots(1, len(fams), figsize=(4.6 * len(fams), 3.6))
    if len(fams) == 1:
        axs = [axs]
    for ax, fam in zip(axs, fams):
        pb, drat = series(rows, fam)
        _draw(ax, fam, pb, drat)
        write_dat(fam, pb, drat, suffix)
        # per-problem figure
        f1, a1 = plt.subplots(figsize=(4.8, 3.6))
        _draw(a1, fam, pb, drat)
        f1.tight_layout()
        out = RES / f"scaling_{fam}{suffix}.png"
        f1.savefig(out, dpi=140); plt.close(f1)
        print(f"wrote {out}")
    fig.tight_layout()
    allout = RES / f"scaling_all{suffix}.png"
    fig.savefig(allout, dpi=140); plt.close(fig)
    print(f"wrote {allout}")


if __name__ == "__main__":
    main()
