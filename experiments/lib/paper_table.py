#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
from pathlib import Path

RES = Path(__file__).resolve().parent.parent.parent / "experiments" / "sbc" / "results"

ORDER = ["clique", "clique_coloring", "schur", "oddcycle", "ramsey",
         "vdw", "matching", "langford", "mutilated", "php"]
DISPLAY = {
    "clique":          ("Clique",    "vp"),
    "clique_coloring": ("Myciel.",   "vp"),
    "schur":           ("Schur",     "vp"),
    "oddcycle":        ("Odd cyc.",  "$x_0{=}0$"),
    "ramsey":          ("Ramsey",    "$x_0{=}0$"),
    "vdw":             ("vdW",       "vp"),
    "matching":        ("Match.",    "transp."),
    "langford":        ("Langf.",    "rev."),
    "mutilated":       ("Mutil.",    "refl."),
    "php":             ("PHP",       "vp"),
}
TO = r"\emph{t/o}"
NA = r"---"


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


def det(v):
    if v is None:
        return TO
    return sci(v) if v >= 1e4 else f"{int(round(v))}"


def sec(v):
    return TO if v is None else f"{v:.3g}"


def spd(v):
    if v is None:
        return NA
    if v >= 1e4:
        s = sci(v)
    elif v >= 10:
        s = f"{v:.0f}"
    elif v >= 1:
        s = f"{v:.1f}"
    else:
        s = f"{v:.2g}"
    return r"{\boldmath\bfseries " + s + "}" if v > 1 else s   # bold a speedup > 1 (SBC helps)


def check_fmt(ns, status, cert_bytes):
    # checker runtime in SECONDS (one unit for the whole column, matching the wall columns)
    if status != "OK" or ns is None:
        return NA
    return f"{ns / 1e9:.3g}"


def load_check():
    """{family: {'none': (ns, status, cert_bytes), 'sbc': ...}} from check_largest.csv (if present)."""
    p = RES / "check_largest.csv"
    out = {}
    if not p.exists():
        return out
    for r in csv.DictReader(open(p)):
        key = "none" if r["regime"] == "none" else "sbc"
        out.setdefault(r["family"], {})[key] = (num(r.get("check_ns")), r.get("status"),
                                                num(r.get("cert_bytes")) or 0)
    return out


def row(r, chk):
    name, sbc = DISPLAY[r["family"]]
    g = lambda k: num(r.get(k))
    c = chk.get(r["family"], {})
    cn = check_fmt(*c.get("none", (None, None, 0)))
    cs = check_fmt(*c.get("sbc", (None, None, 0)))
    cells = [
        name, sbc,
        det(g("det_none_hi")), sec(g("wall_none_hi")),
        det(g("det_sbc_hi")),  sec(g("wall_sbc_hi")),
        spd(g("speedup_det_hi")),  spd(g("speedup_wall_hi")),
        spd(g("speedup_det_geo")), spd(g("speedup_wall_geo")),
        cn, cs,
    ]
    return " & ".join(cells) + r" \\"


def main():
    rows = {r["family"]: r for r in csv.DictReader(open(RES / "sbc_table.csv"))}
    chk = load_check()
    body = "\n".join(row(rows[f], chk) for f in ORDER if f in rows)
    print(r"""\begin{table*}[!t]
\centering
\setlength{\tabcolsep}{4pt}
\resizebox{\ifdim\width>\textwidth \textwidth\else\width\fi}{!}{%
\begin{tabular}{l l r r r r r r r r r r}
\toprule
 &  & \multicolumn{2}{c}{w/o SBC (lg.)} & \multicolumn{2}{c}{w/ SBC (lg.)} & \multicolumn{2}{c}{Speedup (lg.)} & \multicolumn{2}{c}{Speedup (geo.)} & \multicolumn{2}{c}{Check (lg., s)} \\
\cmidrule(lr){3-4}\cmidrule(lr){5-6}\cmidrule(lr){7-8}\cmidrule(lr){9-10}\cmidrule(lr){11-12}
Family & SBC & det & wall\,(s) & det & wall\,(s) & det & wall & det & wall & w/o & w/ \\
\midrule""")
    print(body)
    print(r"""\bottomrule
\end{tabular}}
\caption{Effect of a verified symmetry-breaking constraint (SBC) per family. SBCs: \emph{vp} value precedence, \emph{transp.}\ transposition, \emph{rev.}\ reversal, \emph{refl.}\ reflection. All quantities are at the \emph{largest} instance solved (``lg.''; a size that times out in both regimes is dropped), except the ``geo.'' speedup, a geometric mean over the whole range. We give RoundingSat's \emph{deterministic} time (a machine-independent operation count) and \emph{wall}-clock time (in seconds) without / with the SBC, and the resulting speedups; a speedup ${>}1$ (the SBC helps) is shown in \textbf{bold}. The largest instance per family is: Clique $K_{15}$; Mycielskian $M_4$; Schur at colour count $c{=}4$, its critical $n{=}S(4){+}1{=}45$ (the range spans $c{=}2,3,4$ at criticality $n{=}S(c){+}1$, i.e.\ $n\in\{5,6,7,14,15,45\}$); Odd cycle $C_{51}$; Ramsey $R(3,3)$ on $K_{10}$; van der Waerden $W(3,3)$ at $n{=}28$; perfect Matching on $K_{19}$; Langford $L(2,10)$; the $12{\times}12$ Mutilated board; and Pigeonhole $n{=}12$. ``Check'' is PBLean's \emph{compiled} checker runtime (in seconds; the function \texttt{Lean.ofReduceBool} reduces) on the largest certificate produced in each regime, timed with a native harness reading the certificate at runtime. Checking is feasible everywhere and scales with certificate size, so value precedence — which shrinks the color-symmetric families' certificates by orders of magnitude (Clique $K_{15}$: 391\,MB / 187\,s without $\to$ 10\,KB / 0.006\,s with) — cuts checking cost as it cuts search, while the variable SBCs leave both regimes' certificates large. \emph{t/o} marks a 600\,s solver timeout (its speedup, ``---'', is a lower bound): Schur $c{=}4$, $n{=}45$ is unsolved without the SBC but solved in 42.5\,s with it (its w/-SBC certificate is the 102\,MB one, checked in 49\,s).}
\label{tab:sbc}
\end{table*}""")


if __name__ == "__main__":
    main()
