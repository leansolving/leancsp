#!/usr/bin/env python3
from __future__ import annotations

GC = "CSP.L2S.Proofs.GraphColoringSB"            # graph_coloring_csp
SCH = "CSP.L2S.Proofs.SchurSB"                    # Schur.schur_sb
PHP = "CSP.L2S.Proofs.PigeonholeValuePrecedence"  # Pigeonhole.php_sb
GEN = "CSP.L2S.Backends.PB.Bench.Generators"      # Bench.gen_*
RMS = "CSP.L2S.Proofs.RamseyValuePrecedence"      # ramsey_r33_csp (+ verified vp glue)

# ---------------------------------------------------------------------------
# graph helpers (clique / odd cycle reuse the verified graph_coloring_csp)
# ---------------------------------------------------------------------------
def _edges_lit(edges):
    return "[" + ", ".join(f"({a}, {b})" for a, b in edges) + "]"


def _clique_edges(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def _cycle_edges(n):
    return [(i, (i + 1) % n) for i in range(n)]


def _clique(n):   # Kₙ with n−1 colours (critical: needs n colours)
    return f"graph_coloring_csp {n} {_edges_lit(_clique_edges(n))} {n - 1}"


def _cycle(m):    # C_{2m+1} with 2 colours (critically non-2-colourable)
    n = 2 * m + 1
    return f"graph_coloring_csp {n} {_edges_lit(_cycle_edges(n))} 2"


# Verified end-to-end glue: `glue(inst)` applied to the vp-extended UNSAT cert proof yields
# `¬ base.isSatisfiableInt`, using the family's axiom-clean *_unsat_of_value_precedence theorem.
GCVP = "CSP.L2S.Proofs.GraphColoringValuePrecedence"
SCVP = "CSP.L2S.Proofs.SchurValuePrecedence"
PHVP = "CSP.L2S.Proofs.PigeonholeValuePrecedence"
RMVP = "CSP.L2S.Proofs.RamseyValuePrecedence"


# ---------------------------------------------------------------------------
# critical thresholds + near-critical bands (more points without over-constraining)
# ---------------------------------------------------------------------------
# Hardness scales with the COLOUR count c at criticality n=S(c)+1, NOT with n past it (extra-n
# points within a colour are time-flat — kept only for cert-size scaling).  c=4 (n=45) is the hard
# point: `none` times out, `vp` ≈ 43 s (external-only — cert exceeds the native_decide cap).
SCHUR_BAND = {2: [5, 6, 7], 3: [14, 15], 4: [45]}        # n = S(c)+1 … (S(c)=4,13,44)
# VdW is restricted to k=3 (schur_triple → colour-symmetric → value precedence VERIFIED for any r).
# Hardness scales with the COLOUR count r at criticality (n ≥ W(r,3)), NOT with n past threshold
# (bigger n adds AP constraints → smaller refutation core → easier).  r=4 (W(4,3)=76) is the hard
# point: `none` ~times out, `vp` solves in minutes (external-only — cert exceeds the native_decide cap).
VDW_BAND = [(2, 9), (2, 10), (2, 11), (3, 27), (3, 28), (4, 76)]   # (r, n = W(r,3))
# Ramsey is the diagonal R(3,3) (schur_triple over triangles → vp VERIFIED); scale n above R(3,3)=6.
RAMSEY_N = [6, 7, 8, 9, 10]
LANGFORD_N = [2, 5, 6, 9, 10]                            # UNSAT residues n ≡ 1,2 (mod 4)


def inst(label, nat, expr, colors, **extra):
    """One instance.  `nat` = natural scaling parameter (primary x-axis where single-valued)."""
    d = dict(label=label, nat=nat, expr=expr, colors=colors)
    d.update(extra)
    return d


FAMILIES = {
    # ===== VALUE-symmetric (value precedence is the matched SBC) =====
    "clique": dict(module=GC, axis="n", regimes=["none", "vp"], note="Kₙ /(n−1) colours",
        glue_import=GCVP,
        glue=lambda i: f"graph_coloring_unsat_of_value_precedence {i['nat']} {i['nat'] - 1} "
                       f"{_edges_lit(_clique_edges(i['nat']))}",
        instances=[inst(f"K{n}", n, _clique(n), n - 1) for n in range(3, 16)]),
    "schur": dict(module=SCH, axis="vars", regimes=["none", "vp"], note="critical n=S(c)+1, scale c",
        glue_import=SCVP,
        glue=lambda i: f"Schur.schur_unsat_of_value_precedence {i['nat']} {i['colors']} "
                       f"(Schur.schurTriples {i['nat']})",
        instances=[inst(f"c{c}n{n}", n, f"Schur.schur_sb {n} {c}", c)
                   for c, ns in SCHUR_BAND.items() for n in ns]),
    "vdw": dict(module=GEN, axis="vars", regimes=["none", "vp"],
        note="Van der Waerden W(r,3) via schur_csp_sb (vp verified, any r)", glue_import=SCVP,
        glue=lambda i: f"Schur.schur_unsat_of_value_precedence {i['nat']} {i['colors']} "
                       f"(Bench.vdwTriples {i['nat']})",
        instances=[inst(f"W{r}3n{n}", n, f"Bench.gen_vdw3 {r} {n}", r) for (r, n) in VDW_BAND]),
    "php": dict(module=PHP, axis="h", regimes=["none", "vp"], note="PHP(h+1,h)", glue_import=PHVP,
        glue=lambda i: f"Pigeonhole.php_unsat_of_value_precedence {i['pigeons']} {i['nat']}",
        instances=[inst(f"h{h}", h, f"Pigeonhole.php_sb {h + 1} {h}", h, pigeons=h + 1)
                   for h in range(2, 13)]),
    "clique_coloring": dict(module=GEN, axis="vars", regimes=["none", "vp"],
        note="Mycielskian Mⱼ (χ=j+2) with j+1 colours; triangle-free, χ>clique", glue_import=GCVP,
        glue=lambda i: f"graph_coloring_unsat_of_value_precedence (Bench.mycielskiGraph {i['nat']}).1 "
                       f"{i['nat'] + 1} (Bench.mycielskiFinEdges {i['nat']})",
        instances=[inst(f"M{j}", j, f"Bench.gen_clique_coloring {j}", j + 1) for j in [2, 3, 4]]),

    # ===== BINARY value (2-colour: value precedence encodes as x0=0, but is the VERIFIED constructor) =====
    "ramsey": dict(module=RMS, axis="n", regimes=["none", "vp"],
        note="diagonal R(3,3) 2-colour, schur_triple (vp verified); scale n", glue_import=RMVP,
        glue=lambda i: f"ramsey_unsat_of_value_precedence {i['nat']}",
        instances=[inst(f"R33n{n}", n, f"ramsey_r33_csp {n}", 2) for n in RAMSEY_N]),

    # odd-cycle is a graph_coloring_csp → value precedence is VERIFIED (encodes as x0=0 for 2 colours)
    "oddcycle": dict(module=GC, axis="len", regimes=["none", "vp"],
        note="C_{2m+1} 2-colour (graph_coloring → vp verified, encodes as x0=0)",
        glue_import=GCVP,
        glue=lambda i: f"graph_coloring_unsat_of_value_precedence {i['nat']} {i['colors']} "
                       f"{_edges_lit(_cycle_edges(i['nat']))}",
        instances=[inst(f"C{2 * m + 1}", 2 * m + 1, _cycle(m), 2) for m in range(2, 26)]),

    # ===== VARIABLE-symmetric (lex/reflection variable SBC; verified via *SB.lean) =====
    "mutilated": dict(module=GEN, axis="board", regimes=["none", "var"],
        note="2k×2k mutilated board; diagonal-reflection SBC (verified)",
        var_sbc=lambda i: f"Bench.mutilated_sb {i['k']}",
        glue_import="CSP.L2S.Proofs.MutilatedSB",
        glue=lambda i: f"CSP.L2S.PB.MutilatedSB.mutilated_unsat_of_var {i['k']} (by norm_num)",
        instances=[inst(f"b{2 * k}", 2 * k, f"Bench.gen_mutilated {k}", 2, k=k) for k in range(2, 7)]),
    "matching": dict(module=GEN, axis="verts", regimes=["none", "var"],
        note="perfect matching on K_{2m+1}; vertex-transposition SBC (verified)",
        var_sbc=lambda i: f"Bench.matching_sb {i['m']}",
        glue_import="CSP.L2S.Proofs.MatchingSB",
        glue=lambda i: f"CSP.L2S.PB.MatchingSB.matching_unsat_of_var {i['m']} (by norm_num)",
        instances=[inst(f"K{2 * m + 1}", 2 * m + 1, f"Bench.gen_matching {m}", 2, m=m) for m in range(2, 10)]),
    "langford": dict(module=GEN, axis="n", regimes=["none", "var"],
        note="L(2,n) UNSAT (n≡1,2 mod4); reversal SBC x0≤n-1 (verified)",
        var_sbc=lambda i: f"Bench.langford_sb {i['n']}",
        glue_import="CSP.L2S.Proofs.LangfordSB",
        glue=lambda i: f"(@CSP.L2S.PB.LangfordSB.langford_unsat_of_rev {i['n']} (by norm_num))",
        instances=[inst(f"n{n}", n, f"Bench.gen_langford {n}", 2, n=n) for n in LANGFORD_N]),
}

# All regimes that may appear, with their human-readable SBC description.
SBC_DESC = {"none": "—", "vp": "value_precedence", "x0": "x0=0 (= value precedence)",
            "var": "variable lex/reflection"}


def regime_expr(cfg: dict, it: dict, regime: str) -> str:
    """Full extended-CSP Lean term for `(instance, regime)`."""
    base = it["expr"]
    if regime == "none":
        return base
    if regime == "vp":
        return f"(({base}).addConstraint (value_precedence {it['colors']}))"
    if regime == "x0":
        return f"(({base}).addConstraint (IntConstraint.eq_const 0 0))"
    if regime == "var":
        return f"(({base}).addConstraint ({cfg['var_sbc'](it)}))"
    raise ValueError(regime)
