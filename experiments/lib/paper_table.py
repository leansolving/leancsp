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
    # absolute deterministic op-counts: always scientific, so the column is uniform
    return TO if v is None else sci(v)


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
\caption{Effect of a verified symmetry-breaking constraint (SBC) per family. SBCs: \emph{vp} value precedence, \emph{transp.}\ transposition, \emph{rev.}\ reversal, \emph{refl.}\ reflection. Sizes: Clique $K_3$--$K_{15}$; Myciel.\ $M_2$--$M_4$; Schur $n{=}5$--$45$ (colours $c{=}2$--$4$); Odd cyc.\ $C_5$--$C_{51}$; Ramsey $K_6$--$K_{10}$; vdW $n{=}9$--$28$ (colours $2,3$); Match.\ $K_5$--$K_{19}$; Langf.\ $n{=}2$--$10$; Mutil.\ $4{\times}4$--$12{\times}12$; PHP $n{=}2$--$12$. Columns report, without / with the SBC at the largest instance solved (``lg.''), RoundingSat's \emph{deterministic} operation count and \emph{wall} time (s); the speedups, at that instance and as a geometric mean over the range (``geo.''), with a speedup ${>}1$ in \textbf{bold}; and ``Check'', PBLean's compiled checker time (s) on each regime's largest certificate. \emph{t/o} marks a 600\,s timeout, which can leave the largest-instance speedup incomputable (``---''): Schur is unsolved without the SBC at $c{=}4$, $n{=}45$, so we report its next size, $c{=}3$, $n{=}15$, where value precedence gives a $7.5\times$ deterministic speedup.}
\label{tab:sbc}
\end{table*}""")


if __name__ == "__main__":
    main()
