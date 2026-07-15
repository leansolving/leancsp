#!/usr/bin/env python3
from __future__ import annotations

import csv
import math
import sys
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
REJ = r"\emph{rej.}"   # checker ran and returned false: the certificate did NOT verify


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
    if v >= 1000:
        s = f"{int(round(v)):,}"      # plain, thousands separators (never scientific)
    elif v >= 10:
        s = f"{v:.0f}"
    elif v >= 1:
        s = f"{v:.1f}"
    else:
        s = f"{v:.2g}"
    return r"\textbf{" + s + "}" if v > 1 else s   # bold a speedup > 1 (SBC helps)


def check_fmt(ns_str, status):
    # NATIVE checkProofBool runtime (ns from the compiled checkbench exe) -> seconds.
    # A "FALSE" status means the checker returned false — the cert did not verify — so its timing
    # is not a checking cost and must never render as one.
    if status == "FALSE":
        return REJ
    if status == "TIMEOUT":
        return TO
    v = num(ns_str)
    return NA if v is None else f"{v / 1e9:.3g}"


def pipe_fmt(sec_str, status):
    # IN-LEAN pipeline cost (s): full `lake build` of one csp_unsat_file reflection theorem with a
    # PRECOMPILED checker, net of the fixed per-module build overhead. t/o if it timed out / failed.
    if status in ("TIMEOUT", "BUILD-FAIL"):
        return TO
    v = num(sec_str)
    return NA if v is None else f"{v:.3g}"


def row(r):
    name, sbc = DISPLAY[r["family"]]
    g = lambda k: num(r.get(k))
    cells = [
        name, sbc,
        det(g("det_none_hi")), sec(g("wall_none_hi")),
        det(g("det_sbc_hi")),  sec(g("wall_sbc_hi")),
        spd(g("speedup_det_hi")),  spd(g("speedup_wall_hi")),
        spd(g("speedup_det_geo")), spd(g("speedup_wall_geo")),
        check_fmt(r.get("check_none_hi"), r.get("check_none_status")),                # native
        check_fmt(r.get("check_sbc_hi"), r.get("check_sbc_status")),
        pipe_fmt(r.get("pipe_none_hi"), r.get("pipe_none_status")),                   # in-Lean
        pipe_fmt(r.get("pipe_sbc_hi"), r.get("pipe_sbc_status")),
    ]
    return " & ".join(cells) + r" \\"


def main():
    suffix = ".smoke" if "--smoke" in sys.argv else ""
    rows = {r["family"]: r for r in csv.DictReader(open(RES / f"sbc_table{suffix}.csv"))}
    body = "\n".join(row(rows[f]) for f in ORDER if f in rows)
    print(r"""\begin{table*}[!t]
\centering
\setlength{\tabcolsep}{4pt}
\resizebox{\ifdim\width>\textwidth \textwidth\else\width\fi}{!}{%
\begin{tabular}{l l r r r r r r r r r r r r}
\toprule
 &  & \multicolumn{2}{c}{w/o SBC (lg.)} & \multicolumn{2}{c}{w/ SBC (lg.)} & \multicolumn{2}{c}{Speedup (lg.)} & \multicolumn{2}{c}{Speedup (geo.)} & \multicolumn{2}{c}{Check (native, s)} & \multicolumn{2}{c}{Check (in-Lean, s)} \\
\cmidrule(lr){3-4}\cmidrule(lr){5-6}\cmidrule(lr){7-8}\cmidrule(lr){9-10}\cmidrule(lr){11-12}\cmidrule(lr){13-14}
Family & SBC & det & wall\,(s) & det & wall\,(s) & det & wall & det & wall & w/o & w/ & w/o & w/ \\
\midrule""")
    print(body)
    # ends at \end{tabular}} — the \caption, \label and \end{table*} live outside the
    # auto-generated markers in the paper, so re-splicing never overwrites the caption.
    print(r"""\bottomrule
\end{tabular}}""")


if __name__ == "__main__":
    main()
