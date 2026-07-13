#!/usr/bin/env python3
from __future__ import annotations

# OPB header constants matching CSP/L2S/Backends/PB/Serialize.lean (toOPBString).
_INTSIZE = 6


def _opb(num_vars: int, constraints: list[tuple[list[tuple[int, int, bool]], int]]) -> str:
    """Serialize constraints to OPB text exactly as `toOPBString` does.

    A constraint is `(terms, degree)`; a term is `(coeff, var1based, negated)`.
    Emits `+{coeff} x{v}` or `+{coeff} ~x{v}`, joined by spaces, ` >= {deg} ;`.
    """
    header = f"* #variable= {num_vars} #constraint= {len(constraints)} #equal= 0 intsize= {_INTSIZE}"
    lines = [header]
    for terms, deg in constraints:
        parts = []
        for coeff, v, neg in terms:
            lit = f"~x{v}" if neg else f"x{v}"
            parts.append(f"+{coeff} {lit}")
        lines.append(" ".join(parts) + f" >= {deg} ;")
    return "\n".join(lines) + "\n"


def _cnf(num_vars: int, clauses: list[list[int]]) -> str:
    """Serialize clauses to DIMACS CNF text."""
    lines = [f"p cnf {num_vars} {len(clauses)}"]
    for cl in clauses:
        lines.append(" ".join(str(x) for x in cl) + " 0")
    return "\n".join(lines) + "\n"


def _linear_le(coeffs_vars: list[tuple[int, int]], b: int):
    """Order-encode one linear constraint `Σ k·x ≤ b` over width-1 {0,1} variables
    into a normalized OPB constraint `(terms, degree)`, or None if it normalizes to
    a tautology.  Replicates `encodeLinearLe` + `normalize` of the Lean backend for
    the {0,1} case (gap = 1, maxVal = 1, threshold of var v is OPB var v+1); this is
    the same logic validated byte-for-byte for the mutilated chessboard."""
    sumk = sum(k for k, _ in coeffs_vars)
    terms, shift = [], 0
    for k, v in coeffs_vars:
        if k > 0:
            terms.append((k, v + 1, False))
        elif k < 0:
            terms.append((-k, v + 1, True)); shift += -k
    deg = (sumk - b) + shift
    return (terms, deg) if deg > 0 else None


# --------------------------------------------------------------------------- #
# Pigeonhole php_(n+1)_n : n+1 pigeons into n holes, all distinct.
# Integer var per pigeon over domain {1..n}; alldifferent.
# (Resolution-hard: Haken 1985.  Polynomial cutting-planes: Cook-Coullard-Turan.)
# --------------------------------------------------------------------------- #

def php_opb(n: int) -> str:
    """OPB for php_(n+1)_n (n = number of holes).  Matches `encodeCSP php_(n+1)_n`
    (corpus CSPs in `Tests/lean/35_pigeonhole.lean`, proved in
    `Problems/Pigeonhole.lean`)."""
    assert n >= 2
    pigeons = n + 1
    width = n - 1                       # thresholds per pigeon

    def thr(i: int, j: int) -> int:     # 1-based OPB var for t_{i,j}
        return i * width + j + 1

    cons: list[tuple[list[tuple[int, int, bool]], int]] = []
    # monotonicity: t_{i,j+1} + ~t_{i,j} >= 1  (pos then neg, matching Lean order)
    for i in range(pigeons):
        for j in range(width - 1):
            cons.append(([(1, thr(i, j + 1), False), (1, thr(i, j), True)], 1))
    # alldifferent over values {1..n}: for each val, "at most one pigeon = val".
    for val in range(1, n + 1):
        terms: list[tuple[int, int, bool]] = []
        for i in range(pigeons):
            if val == 1:
                terms.append((1, thr(i, 0), True))               # ~t_{i,0}
            elif val == n:
                terms.append((1, thr(i, n - 2), False))          #  t_{i,n-2}
            else:
                terms.append((1, thr(i, val - 2), False))        #  t_{i,val-2}
                terms.append((1, thr(i, val - 1), True))         # ~t_{i,val-1}
        cons.append((terms, n))
    return _opb(pigeons * width, cons)


def php_cnf(n: int) -> str:
    """Natural DIMACS CNF for php_(n+1)_n (the classic Haken pigeonhole core).

    Variable p_{i,h} ("pigeon i in hole h") is CNF var i*n + h + 1.
    Clauses: each pigeon in >=1 hole; no two pigeons share a hole.
    """
    assert n >= 2
    pigeons = n + 1

    def p(i: int, h: int) -> int:
        return i * n + h + 1

    clauses: list[list[int]] = []
    for i in range(pigeons):                                  # >=1 hole per pigeon
        clauses.append([p(i, h) for h in range(n)])
    for h in range(n):                                        # <=1 pigeon per hole
        for i in range(pigeons):
            for i2 in range(i + 1, pigeons):
                clauses.append([-p(i, h), -p(i2, h)])
    return _cnf(pigeons * n, clauses)


# --------------------------------------------------------------------------- #
# Mutilated chessboard: 2k x 2k board minus the two opposite (same-colour)
# corners (0,0) and (N-1,N-1).  Boolean var per domino placement; per-cell
# exactly-one (exact cover).  No tiling: colour imbalance of 2.
# (Resolution-hard: Alekhnovich 2004.  Polynomial cutting-planes: colour count.)
# --------------------------------------------------------------------------- #

def _mutilated_geometry(k: int):
    """Return (num_placements, covers) for a 2k x 2k mutilated board.

    Placements are enumerated in the same order as MutilatedChessboard.lean:
    row-major over cells; for each present cell, its right-neighbour horizontal
    domino (if present) then its down-neighbour vertical domino (if present).
    `covers` is the list of (cell, sorted_placement_indices) in row-major cell
    order over present cells.
    """
    N = 2 * k
    removed = {(0, 0), (N - 1, N - 1)}

    def present(r, c):
        return 0 <= r < N and 0 <= c < N and (r, c) not in removed

    place_id: dict[tuple, int] = {}     # placement key -> index
    nxt = 0
    for r in range(N):
        for c in range(N):
            if not present(r, c):
                continue
            if present(r, c + 1):                       # horizontal (r,c)-(r,c+1)
                place_id[("H", r, c)] = nxt; nxt += 1
            if present(r + 1, c):                       # vertical   (r,c)-(r+1,c)
                place_id[("V", r, c)] = nxt; nxt += 1

    covers = []
    for r in range(N):
        for c in range(N):
            if not present(r, c):
                continue
            cov = []
            if ("H", r, c) in place_id:        cov.append(place_id[("H", r, c)])      # right
            if ("H", r, c - 1) in place_id:    cov.append(place_id[("H", r, c - 1)])  # left
            if ("V", r, c) in place_id:        cov.append(place_id[("V", r, c)])      # down
            if ("V", r - 1, c) in place_id:    cov.append(place_id[("V", r - 1, c)])  # up
            covers.append(((r, c), sorted(cov)))
    return nxt, covers


def mutilated_opb(k: int) -> str:
    """OPB for the 2k x 2k mutilated chessboard.  Matches `encodeCSP` of the
    `Problems/MutilatedChessboard{,6}.lean` instances (k=2, k=3)."""
    nplace, covers = _mutilated_geometry(k)
    cons: list[tuple[list[tuple[int, int, bool]], int]] = []
    for _cell, cov in covers:
        # exactly-one sum_eq = 1 over width-1 {0,1} vars:
        #   <= half:  sum x_p <= 1   ->  sum  x_p  >= |cov|-1
        #   >= half:  sum x_p >= 1   ->  sum ~x_p  >= 1
        cons.append(([(1, p + 1, False) for p in cov], len(cov) - 1))
        cons.append(([(1, p + 1, True) for p in cov], 1))
    return _opb(nplace, cons)


def mutilated_cnf(k: int) -> str:
    """Natural DIMACS CNF for the 2k x 2k mutilated chessboard (exact cover)."""
    nplace, covers = _mutilated_geometry(k)
    clauses: list[list[int]] = []
    for _cell, cov in covers:
        clauses.append([p + 1 for p in cov])                       # at-least-one
        for a in range(len(cov)):                                  # at-most-one
            for b in range(a + 1, len(cov)):
                clauses.append([-(cov[a] + 1), -(cov[b] + 1)])
    return _cnf(nplace, clauses)


# --------------------------------------------------------------------------- #
# Odd cycle C_n 2-colourability (n odd) -- the EASY non-separation baseline.
#
# The odd cycle C_n on vertices 0..n-1 (edges (i, i+1 mod n)) is not 2-colourable.
# This SCALES the committed `k3_2col` (C_3, the smallest odd cycle).  Each vertex
# is an integer colour variable over the binary domain {1,2} (a single threshold
# bit, so order-encoding monotonicity is empty); each edge (u,v) is a `not_equal`
# constraint, encoded via the binary not-all-equal encoder into the two clauses
#   ~x_u + ~x_v >= 1   (not both colour 1)   and   x_u + x_v >= 1   (not both 2),
# in that order (matching `encodePattern`'s `not_equal` case).
# All coefficients are 0/1 -- no Big-M, no binary place values -- so unlike PHP /
# mutilated this is EASY for both cutting planes AND resolution: the PB
# certificate grows linearly and the resolution (DRAT) proof stays small too.
# That is the point: odd cycle is the control that isolates the PHP / mutilated
# walls as resolution-specific, not an artifact of the encoding pipeline.
#
# Vertex i is OPB variable i+1 (width 1); this matches the generic encoding of
# `c5/c7/c9_2col` (corpus `Tests/lean/02_color.lean`, proved in
# `Problems/OddCycle.lean`) exactly.
# --------------------------------------------------------------------------- #

def _cycle_edges(n: int) -> list[tuple[int, int]]:
    assert n >= 3 and n % 2 == 1, "odd cycle needs odd n >= 3"
    return [(i, (i + 1) % n) for i in range(n)]


def oddcycle_opb(n: int) -> str:
    """OPB for the odd cycle C_n 2-colouring (n odd).  Matches `encodeCSP` of the
    `cN_2col` instances (negated clause first, as `encodePattern` emits)."""
    cons: list[tuple[list[tuple[int, int, bool]], int]] = []
    for u, v in _cycle_edges(n):
        cons.append(([(1, u + 1, True), (1, v + 1, True)], 1))     # ~x_u + ~x_v >= 1
        cons.append(([(1, u + 1, False), (1, v + 1, False)], 1))   # x_u + x_v >= 1
    return _opb(n, cons)


def oddcycle_cnf(n: int) -> str:
    """Natural DIMACS CNF for the odd cycle C_n 2-colouring (the canonical UNSAT
    2-SAT instance): one Boolean per vertex, per edge (u,v) the clauses
    (x_u v x_v) and (~x_u v ~x_v)."""
    clauses: list[list[int]] = []
    for u, v in _cycle_edges(n):
        clauses.append([u + 1, v + 1])
        clauses.append([-(u + 1), -(v + 1)])
    return _cnf(n, clauses)


# --------------------------------------------------------------------------- #
# CLI: `pbgen.py <family> <size> <opb|cnf>` -> writes to stdout.
# --------------------------------------------------------------------------- #
if __name__ == "__main__":
    import sys
    fam, size, fmt = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    gen = {
        ("php", "opb"): php_opb, ("php", "cnf"): php_cnf,
        ("mutilated", "opb"): mutilated_opb, ("mutilated", "cnf"): mutilated_cnf,
        ("oddcycle", "opb"): oddcycle_opb, ("oddcycle", "cnf"): oddcycle_cnf,
    }[(fam, fmt)]
    sys.stdout.write(gen(size))
