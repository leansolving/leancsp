#!/usr/bin/env python3
"""Deterministically generate the paper's SBC table (tab:sbc) from sbc_table.csv.

Per family: solving cost without / with the SBC at the largest instance, for both RoundingSat's
deterministic time (a machine-independent op-count) and wall time (s); the speedup for each metric
at the largest instance and as a geometric mean over the range; and our pipeline's own cost — the
in-Lean PBLean checker runtime (``Check'', µs) and the full reflected-term cost including Lean's
compilation (``Full'', s), each as a geometric mean and maximum over the family's instances. The
checking cost is essentially the same with and without the SBC, so it is pooled over both regimes.
A ``t/o'' cell timed out (600 s), so its speedup is a lower bound (``---'').

To fit AAAI's page width the family / SBC names are abbreviated and the size range is compact; the
whole booktabs table* is wrapped in a shrink-to-fit \\resizebox (never enlarged past its natural
width).

Usage: python experiments/lib/paper_table.py    # prints the LaTeX block to stdout
"""
from __future__ import annotations

import csv
import math
from pathlib import Path

RES = Path(__file__).resolve().parent.parent.parent / "experiments" / "sbc" / "results"

# family → (abbreviated name, SBC label, sizes formatter(lo, hi))  — order follows the paper
ORDER = ["clique", "clique_coloring", "schur", "oddcycle", "ramsey",
         "vdw", "matching", "langford", "mutilated", "php"]
DISPLAY = {
    "clique":          ("Clique",    "vp",          lambda lo, hi: f"{lo}--{hi}"),
    "clique_coloring": ("Myciel.",   "vp",          lambda lo, hi: f"{lo}--{hi}"),
    "schur":           ("Schur",     "vp",          lambda lo, hi: f"{lo}--{hi}"),
    "oddcycle":        ("Odd cyc.",  "$x_0{=}0$",   lambda lo, hi: f"{lo}--{hi}"),
    "ramsey":          ("Ramsey",    "$x_0{=}0$",   lambda lo, hi: f"{lo}--{hi}"),
    "vdw":             ("vdW",       "vp",          lambda lo, hi: f"{lo}--{hi}"),
    "matching":        ("Match.",    "transp.",     lambda lo, hi: f"{lo}--{hi}"),
    "langford":        ("Langf.",    "rev.",        lambda lo, hi: f"{lo}--{hi}"),
    "mutilated":       ("Mutil.",    "refl.",       lambda lo, hi: f"{lo}--{hi}"),
    "php":             ("PHP",       "vp",          lambda lo, hi: f"{lo}--{hi}"),
}
TO = r"\emph{t/o}"          # timed out at 600 s
NA = r"---"                 # not applicable (speedup against a timed-out run)


def num(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def sci(v):
    e = int(math.floor(math.log10(abs(v))))
    m = v / 10 ** e
    if round(m, 1) >= 10:
        m, e = m / 10, e + 1
    return f"${m:.1f}{{\\times}}10^{{{e}}}$"


def det(v):                                    # deterministic op-count (or timeout)
    if v is None:
        return TO
    return sci(v) if v >= 1e4 else f"{int(round(v))}"


def sec(v):                                    # a time in seconds (or timeout)
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


def us(v):                                     # a checker time in microseconds
    return NA if v is None else f"{int(round(v))}"


def row(r):
    name, sbc, sizes_fmt = DISPLAY[r["family"]]
    g = lambda k: num(r.get(k))
    cells = [
        name, sbc, sizes_fmt(int(r["size_lo"]), int(r["size_hi"])),
        det(g("det_none_hi")), sec(g("wall_none_hi")),          # w/o SBC (largest)
        det(g("det_sbc_hi")),  sec(g("wall_sbc_hi")),           # w/ SBC (largest)
        spd(g("speedup_det_hi")),  spd(g("speedup_wall_hi")),   # speedup at largest
        spd(g("speedup_det_geo")), spd(g("speedup_wall_geo")),  # speedup geomean
        us(g("check_geo_us")),  us(g("check_max_us")),          # checker runtime µs (geo, max)
        sec(g("verify_geo_s")), sec(g("verify_max_s")),         # full incl. compilation s (geo, max)
    ]
    return " & ".join(cells) + r" \\"


def main():
    rows = {r["family"]: r for r in csv.DictReader(open(RES / "sbc_table.csv"))}
    body = "\n".join(row(rows[f]) for f in ORDER if f in rows)
    print(r"""\begin{table*}[!t]
\centering
\setlength{\tabcolsep}{4pt}
\resizebox{\ifdim\width>\textwidth \textwidth\else\width\fi}{!}{%
\begin{tabular}{l l l r r r r r r r r r r r r}
\toprule
 &  &  & \multicolumn{2}{c}{w/o SBC} & \multicolumn{2}{c}{w/ SBC} & \multicolumn{2}{c}{Speedup (lg.)} & \multicolumn{2}{c}{Speedup (geo.)} & \multicolumn{2}{c}{Check ($\mu$s)} & \multicolumn{2}{c}{Full (s)} \\
\cmidrule(lr){4-5}\cmidrule(lr){6-7}\cmidrule(lr){8-9}\cmidrule(lr){10-11}\cmidrule(lr){12-13}\cmidrule(lr){14-15}
Family & SBC & Sizes & det & wall & det & wall & det & wall & det & wall & geo & max & geo & max \\
\midrule""")
    print(body)
    print(r"""\bottomrule
\end{tabular}}
\caption{Effect of a verified symmetry-breaking constraint (SBC) per family. SBCs: \emph{vp} value precedence, \emph{transp.}\ transposition, \emph{rev.}\ reversal, \emph{refl.}\ reflection. ``Sizes'' is the size-parameter range ($K_n$ for Clique/Match./Ramsey, $M_j$ for Myciel., $C_n$ for Odd cyc., board side $2k$ for Mutil., $n$ otherwise). For each of RoundingSat's \emph{deterministic} time (a machine-independent operation count) and \emph{wall}-clock time (s), we give the solving cost without / with the constraint at the \emph{largest} instance, and the speedup both there (``lg.'') and as the geometric mean over the range (``geo.''). ``Check'' is the in-Lean PBLean checker runtime ($\mu$s) and ``Full'' the whole reflected-term cost \emph{including Lean's compilation} (s, dominated by compilation --- overhead outside the checker, listed for honesty); both are pooled over the two regimes (checking cost is essentially SBC-independent) and given as a geometric mean and maximum over the family's instances. \emph{t/o} marks a 600\,s timeout (its speedup, ``---'', is a lower bound): Schur $c{=}4$, $n{=}45$ is unsolved without the SBC but solved in 42.5\,s with it, and $W(4,3)$ ($n{=}76$) is out of reach for both regimes.}
\label{tab:sbc}
\end{table*}""")


if __name__ == "__main__":
    main()
