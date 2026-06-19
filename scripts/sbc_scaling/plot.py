#!/usr/bin/env python3
"""Plot the SBC scaling results: search effort, certificate size, and verification time
across the three regimes (none / x0 / value-precedence).

Reads results/sbc/sbc_scaling.csv (+ sbc_scaling_lean.csv) and writes per-family PNGs and a
speedup summary to results/sbc/.
"""
from __future__ import annotations

import csv
from collections import defaultdict
from pathlib import Path

import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

REPO = Path(__file__).resolve().parent.parent.parent
# results subdir: `python plot.py [sbc|sbc_v2|sbc_v3]` (default sbc_v3)
RES = REPO / "results" / (sys.argv[1] if len(sys.argv) > 1 else "sbc_v3")
REGIMES = ["none", "x0", "vp", "var"]
STYLE = {"none": ("o-", "#d62728"), "x0": ("s-", "#ff7f0e"),
         "vp": ("^-", "#2ca02c"), "var": ("D-", "#1f77b4")}
LABEL = {"none": "no SBC", "x0": "x₀=0 (= value prec.)",
         "vp": "value precedence", "var": "variable lex/refl."}
# Multi-parameter families have no meaningful single natural axis → plot vs #PB variables.
VARS_AXIS = {"vars"}


def load():
    ext = list(csv.DictReader(open(RES / "sbc_scaling.csv")))
    return ext


def _xkey(rows, fam):
    """`pb_vars` for multi-parameter families, else the natural `size_param`."""
    axis = next((r.get("axis", "") for r in rows if r["family"] == fam), "")
    return ("pb_vars", "#PB variables") if axis in VARS_AXIS else ("size_param", axis or "size")


def _series(rows, fam, regime, ykey, xcol):
    pts = [(int(r[xcol]), r[ykey]) for r in rows
           if r["family"] == fam and r["regime"] == regime
           and r["roundingsat_status"] == "UNSAT" and r.get(ykey) and r.get(xcol)]
    pts.sort()
    return [p[0] for p in pts], [float(p[1]) for p in pts]


def plot_family(rows, fam, logscale=True):
    xcol, xlabel = _xkey(rows, fam)
    xunit = f"{xlabel} (vars)" if xcol == "pb_vars" else f"{xlabel} (problem parameter)"
    fig, axs = plt.subplots(1, 3, figsize=(15, 4.2))
    for regime in REGIMES:
        mk, col = STYLE[regime]
        for ax, key in ((axs[0], "rsat_det_time"), (axs[1], "rsat_conflicts"),
                        (axs[2], "kernel_cert_chars")):
            x, y = _series(rows, fam, regime, key, xcol)
            if x:
                ax.plot(x, y, mk, color=col, label=LABEL[regime])
    tag = "log y" if logscale else "linear y"
    axs[0].set(title=f"{fam}: roundingsat deterministic time ({tag})",
               xlabel=xunit, ylabel="deterministic time (ops)")
    axs[1].set(title=f"{fam}: conflicts", xlabel=xunit, ylabel="conflicts (count)")
    axs[2].set(title=f"{fam}: kernel certificate size ({tag})",
               xlabel=xunit, ylabel="certificate size (chars)")
    if logscale:
        axs[0].set_yscale("log"); axs[2].set_yscale("log")
    for ax in axs:
        ax.grid(True, alpha=0.3)
        if ax.get_legend_handles_labels()[0]:
            ax.legend()
    fig.tight_layout()
    out = RES / (f"sbc_{fam}.png" if logscale else f"sbc_{fam}_linear.png")
    fig.savefig(out, dpi=110); plt.close(fig)
    print(f"wrote {out}")


def speedup_table(rows):
    by = defaultdict(dict)
    for r in rows:
        if r["roundingsat_status"] == "UNSAT" and r.get("rsat_det_time"):
            by[(r["family"], r["size_param"])][r["regime"]] = int(r["rsat_det_time"])
    lines = ["family,size,det_none,det_x0,det_vp,det_var,speedup_x0,speedup_vp,speedup_var"]
    for (fam, size), d in sorted(by.items()):
        n = d.get("none"); x0 = d.get("x0"); vp = d.get("vp"); var = d.get("var")
        sx = f"{n/x0:.1f}" if n and x0 else ""
        sv = f"{n/vp:.1f}" if n and vp else ""
        sr = f"{n/var:.1f}" if n and var else ""
        lines.append(f"{fam},{size},{n or ''},{x0 or ''},{vp or ''},{var or ''},{sx},{sv},{sr}")
    (RES / "sbc_speedup.csv").write_text("\n".join(lines) + "\n")
    print(f"wrote {RES / 'sbc_speedup.csv'}")
    print("\n".join(lines))


def main():
    ext = load()
    fams = sorted({r["family"] for r in ext})
    for fam in fams:
        plot_family(ext, fam, logscale=True)    # current log-y figures (sbc_<fam>.png)
        plot_family(ext, fam, logscale=False)   # new linear-y figures (sbc_<fam>_linear.png)
    speedup_table(ext)


if __name__ == "__main__":
    main()
