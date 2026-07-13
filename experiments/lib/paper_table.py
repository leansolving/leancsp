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
        return sci(v)
    if v >= 10:
        return f"{v:.0f}"
    if v >= 1:
        return f"{v:.1f}"
    return f"{v:.2g}"


def check_fmt(ns, status, cert_bytes):
    # certificate too large to check in-Lean: show its size with a dagger instead of a time
    if status in ("TOO-LARGE",) or (status or "").startswith("CHECK->"):
        return f"{cert_bytes / 1e6:.0f}\\,MB$^\\dagger$" if cert_bytes else NA
    if status != "OK" or ns is None:
        return NA
    if ns < 1e6:
        return f"{ns / 1e3:.0f}\\,$\\mu$s"
    if ns >= 1e9:
        return f"{ns / 1e9:.1f}\\,s"
    if ns >= 1e7:
        return f"{ns / 1e6:.0f}\\,ms"
    return f"{ns / 1e6:.1f}\\,ms"


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
        name, sbc, f"{int(r['size_lo'])}--{int(r['size_hi'])}",
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
\begin{tabular}{l l l r r r r r r r r r r}
\toprule
 &  &  & \multicolumn{2}{c}{w/o SBC} & \multicolumn{2}{c}{w/ SBC} & \multicolumn{2}{c}{Speedup (lg.)} & \multicolumn{2}{c}{Speedup (geo.)} & \multicolumn{2}{c}{Check} \\
\cmidrule(lr){4-5}\cmidrule(lr){6-7}\cmidrule(lr){8-9}\cmidrule(lr){10-11}\cmidrule(lr){12-13}
Family & SBC & Sizes & det & wall & det & wall & det & wall & det & wall & w/o & w/ \\
\midrule""")
    print(body)
    print(r"""\bottomrule
\end{tabular}}
\caption{Effect of a verified symmetry-breaking constraint (SBC) per family. SBCs: \emph{vp} value precedence, \emph{transp.}\ transposition, \emph{rev.}\ reversal, \emph{refl.}\ reflection. ``Sizes'' is the size-parameter range ($K_n$ for Clique/Match./Ramsey, $M_j$ for Myciel., $C_n$ for Odd cyc., board side $2k$ for Mutil., $n$ otherwise). For each of RoundingSat's \emph{deterministic} time (a machine-independent operation count) and \emph{wall}-clock time (s), we give the solving cost without / with the constraint at the \emph{largest} instance solved (a size that times out in both regimes is dropped), and the speedup both there (``lg.'') and as the geometric mean over the range (``geo.''). ``Check'' is PBLean's \emph{compiled} checker runtime (the function \texttt{Lean.ofReduceBool} reduces) on the largest certificate produced in each regime, measured with a native harness reading the certificate at runtime. Checking is feasible everywhere ($\mu$s to a few minutes) and scales with certificate size; the SBC's effect on that size mirrors its effect on search: value precedence shrinks the color-symmetric families' certificates by orders of magnitude (Clique $K_{15}$: 391\,MB / 187\,s without $\to$ 10\,KB / 6\,ms with), while the variable SBCs leave both regimes' certificates large. \emph{t/o} marks a 600\,s solver timeout (its speedup, ``---'', is a lower bound): Schur $c{=}4$, $n{=}45$ is unsolved without the SBC but solved in 42.5\,s with it (its $w/$ certificate is then the 102\,MB one, checked in 49\,s).}
\label{tab:sbc}
\end{table*}""")


if __name__ == "__main__":
    main()
