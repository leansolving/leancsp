#!/usr/bin/env python3
"""Deterministically generate the paper's SBC table (tab:sbc) from sbc_table.csv.

Columns: family, SBC, sizes; solving times at the largest instance without / with the SBC
(deterministic op-count and wall seconds); speedup deterministic/wall at the largest instance and
as a geometric mean over the range; and the in-Lean PBLean checking time (geomean µs) without /
with the SBC. A `t/o` cell means the solver timed out (600 s) at that instance, so the
corresponding speedup is a lower bound and shown as `---`.

The 13-column table is wide, so it is emitted as a full-width table* wrapped in a
shrink-to-fit \\resizebox (never enlarges past its natural width), with booktabs rules — fits the
AAAI two-column page width without a manual font change.

Usage: python experiments/lib/paper_table.py    # prints the LaTeX block to stdout
"""
from __future__ import annotations

import csv
import math
from pathlib import Path

RES = Path(__file__).resolve().parent.parent.parent / "experiments" / "sbc" / "results"

# family → (display name, SBC label, sizes-range formatter(lo, hi))  — order follows the paper
ORDER = ["clique", "clique_coloring", "schur", "oddcycle", "ramsey",
         "vdw", "matching", "langford", "mutilated", "php"]
DISPLAY = {
    "clique":          ("Clique $K_n$",       "value prec.",   lambda lo, hi: f"$K_{{{lo}}}$--$K_{{{hi}}}$"),
    "clique_coloring": ("Clique-col.\\ $M_j$", "value prec.",   lambda lo, hi: f"$M_{{{lo}}}$--$M_{{{hi}}}$"),
    "schur":           ("Schur",              "value prec.",   lambda lo, hi: f"$n{{=}}{lo}$--${hi}$"),
    "oddcycle":        ("Odd cycle $C_n$",    "$x_0{=}0$",     lambda lo, hi: f"$C_{{{lo}}}$--$C_{{{hi}}}$"),
    "ramsey":          ("Ramsey $R(3,3)$",    "$x_0{=}0$",     lambda lo, hi: f"$K_{{{lo}}}$--$K_{{{hi}}}$"),
    "vdw":             ("Van der Waerden",    "value prec.",   lambda lo, hi: f"$n{{=}}{lo}$--${hi}$"),
    "matching":        ("Matching $K_n$",     "transposition", lambda lo, hi: f"$K_{{{lo}}}$--$K_{{{hi}}}$"),
    "langford":        ("Langford $L(2,n)$",  "reversal",      lambda lo, hi: f"$n{{=}}{lo}$--${hi}$"),
    "mutilated":       ("Mutilated",          "reflection",    lambda lo, hi: f"${lo}{{\\times}}{lo}$--${hi}{{\\times}}{hi}$"),
    "php":             ("Pigeonhole",         "value prec.",   lambda lo, hi: f"$n{{=}}{lo}$--${hi}$"),
}
TO = r"\emph{t/o}"          # timed out at 600 s
NA = r"---"                 # not applicable (speedup against a timed-out run)


def num(x):
    try:
        v = float(x)
        return v if v != 0 else 0.0
    except (TypeError, ValueError):
        return None


def sci(v):
    e = int(math.floor(math.log10(abs(v))))
    m = v / 10 ** e
    if round(m, 1) >= 10:                      # 9.96 -> 1.0e(e+1)
        m, e = m / 10, e + 1
    return f"${m:.1f}{{\\times}}10^{{{e}}}$"


def det(v):                                    # deterministic op-count (or timeout)
    if v is None:
        return TO
    return sci(v) if v >= 1e4 else f"{int(round(v))}"


def wall(v):                                   # wall seconds (or timeout)
    return TO if v is None else f"{v:.3g}"


def spd(v):                                    # speedup ratio (or n/a against a timeout)
    if v is None:
        return NA
    if v >= 1e4:
        return sci(v)
    if v >= 10:
        return f"{v:.0f}"
    if v >= 1:
        return f"{v:.1f}"
    return f"{v:.2g}"


def chk(v):                                    # PBLean checking time, µs
    return NA if v is None else f"{int(round(v))}"


def row(r):
    fam = r["family"]
    name, sbc, sizes_fmt = DISPLAY[fam]
    lo, hi = int(r["size_lo"]), int(r["size_hi"])
    g = lambda k: num(r.get(k))
    cells = [
        name, sbc, sizes_fmt(lo, hi),
        det(g("det_none_hi")), wall(g("wall_none_hi")),          # w/o SBC (largest)
        det(g("det_sbc_hi")),  wall(g("wall_sbc_hi")),           # w/ SBC (largest)
        spd(g("speedup_det_hi")),  spd(g("speedup_wall_hi")),    # speedup at largest
        spd(g("speedup_det_geo")), spd(g("speedup_wall_geo")),   # speedup geomean
        chk(g("check_none_geo_us")), chk(g("check_sbc_geo_us")), # checking time (µs)
    ]
    return " & ".join(cells) + r" \\"


def main():
    rows = {r["family"]: r for r in csv.DictReader(open(RES / "sbc_table.csv"))}
    body = "\n".join(row(rows[f]) for f in ORDER if f in rows)
    print(r"""\begin{table*}[!t]
\centering
\setlength{\tabcolsep}{4pt}
\resizebox{\ifdim\width>\textwidth \textwidth\else\width\fi}{!}{%
\begin{tabular}{l l l r r r r r r r r r r}
\toprule
 &  &  & \multicolumn{2}{c}{w/o SBC} & \multicolumn{2}{c}{w/ SBC} & \multicolumn{2}{c}{Speedup (largest)} & \multicolumn{2}{c}{Speedup (geo.\ mean)} & \multicolumn{2}{c}{Check ($\mu$s)} \\
\cmidrule(lr){4-5}\cmidrule(lr){6-7}\cmidrule(lr){8-9}\cmidrule(lr){10-11}\cmidrule(lr){12-13}
Family & SBC & Sizes & det. & wall & det. & wall & det. & wall & det. & wall & w/o & w/ \\
\midrule""")
    print(body)
    print(r"""\bottomrule
\end{tabular}}
\caption{Effect of a verified symmetry-breaking constraint (SBC) per family. ``Sizes'' is the range of the family's size parameter. For each of RoundingSat's \emph{deterministic} time (a machine-independent operation count) and \emph{wall}-clock time (seconds), we report the solving cost without (``w/o SBC'') and with (``w/ SBC'') the constraint at the \emph{largest} instance, and the resulting speedup both at the largest instance and as the geometric mean of the per-instance speedups over the whole range. ``Check'' is the geometric mean of PBLean's in-Lean certificate-checking time ($\mu$s), without / with the SBC. \emph{t/o} marks a run that timed out at \SI{600}{\second} (its speedup, ``\,---\,'', is then a lower bound): Schur $c{=}4$, $n{=}45$ is unsolved without the constraint but solved in \SI{42.5}{\second} with it, and the van der Waerden number $W(4,3)$ ($n{=}76$) is out of reach for both regimes.}
\label{tab:sbc}
\end{table*}""")


if __name__ == "__main__":
    main()
