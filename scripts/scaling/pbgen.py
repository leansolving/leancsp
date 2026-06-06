#!/usr/bin/env python3
"""Instance generators for the verified-PB scaling study.

Each function returns the *exact text* of an instance file for one of three
families, in two formats:

  * OPB  -- the pseudo-Boolean order-encoding consumed by RoundingSat, byte-for-byte
           identical to what the verified in-Lean encoder
           (`CSP/L2S/Backends/PB/*.lean`) produces.  Identity is asserted by
           `validate.py`, which diffs these against ground-truth dumps from the
           real Lean encoder at every committed size.
  * CNF  -- the natural DIMACS clause encoding of the *same* instance, used for the
           DRAT (resolution) contrast on the resolution-hard families.

The OPB layout mirrors the Lean pipeline exactly:
  - integer variable `i` with finite domain has `width = |domain|-1` threshold
    bits `t_{i,0..width-1}`, where `t_{i,j}` denotes "value <= domain[j]";
  - variables are numbered flat `[ thresholds, by variable ]` (no Booleans here),
    so threshold `t_{i,j}` is 1-based OPB variable `offset(i)+j+1` with
    `offset(i) = sum of widths of variables < i`;
  - `monotonicity` (staircase) clauses `t_{i,j+1} + ~t_{i,j} >= 1`;
  - linear/alldifferent constraints are order-encoded then `normalize`d to
    non-negative coefficients (`a*L = |a|*~L + a` for `a<0`), dropping the
    constant into the degree.
See `docs/SCALING.md` and `docs/ADDING_UNSAT_INSTANCES.md` for the derivation.
"""

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
    """OPB for php_(n+1)_n (n = number of holes).  Matches Pigeonhole.lean."""
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
    """OPB for the 2k x 2k mutilated chessboard.  Matches MutilatedChessboard.lean."""
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
# Ripple-carry adder, w-bit -- the EASY linear baseline (not resolution-hard).
#
# The committed in-Lean instance (RippleCarry.lean) folds the gate semantics into
# a single linear full-adder identity inside the Lean proof, leaving an O(1)
# 4-constraint OPB regardless of w.  To exhibit the *linear* scaling of the
# order-encoding pipeline itself, this variant encodes the adder explicitly:
#   - carry-in c0 = 0;
#   - per bit i:  a_i + b_i + c_i = s_i + 2 c_{i+1}   (the full-adder identity);
#   - a one-sided correctness miter  Result >= A + B + 1  (UNSAT, since the
#     identities force Result = A + B).
# Everything is linear over {0,1}, so it rides encodeLinearLe (no Big-M, no aux)
# through the SAME order-encoding pipeline validated for PHP / mutilated.  The
# cutting-planes refutation telescopes the carries -- a single linear combination,
# certificate size linear in w.
#
# Variable layout (0-based, all width-1 {0,1}):
#   a_i = i, b_i = w+i, s_i = 2w+i  (i in 0..w-1);  c_i = 3w+i  (i in 0..w).
# --------------------------------------------------------------------------- #

def ripple_linear_opb(w: int) -> str:
    """OPB for the w-bit ripple-carry adder correctness query (linear baseline)."""
    def a(i): return i
    def b(i): return w + i
    def s(i): return 2 * w + i
    def c(i): return 3 * w + i
    nvars = 4 * w + 1

    cons = []

    def add_eq(terms):                       # Σ k·x = 0  ->  two ≤ halves
        for sgn in (1, -1):
            r = _linear_le([(sgn * k, v) for k, v in terms], 0)
            if r:
                cons.append(r)

    add_eq([(1, c(0))])                                  # c0 = 0
    for i in range(w):                                   # a_i + b_i + c_i - s_i - 2 c_{i+1} = 0
        add_eq([(1, a(i)), (1, b(i)), (1, c(i)), (-1, s(i)), (-2, c(i + 1))])
    # miter: Σ2^i a + Σ2^i b - Σ2^i s - 2^w c_w >= 1  ==  -(...) <= -1
    miter = ([(-(1 << i), a(i)) for i in range(w)]
             + [(-(1 << i), b(i)) for i in range(w)]
             + [((1 << i), s(i)) for i in range(w)]
             + [((1 << w), c(w))])
    r = _linear_le(miter, -1)
    if r:
        cons.append(r)
    return _opb(nvars, cons)


# --------------------------------------------------------------------------- #
# CLI: `pbgen.py <family> <size> <opb|cnf>` -> writes to stdout.
# --------------------------------------------------------------------------- #
if __name__ == "__main__":
    import sys
    fam, size, fmt = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    gen = {
        ("php", "opb"): php_opb, ("php", "cnf"): php_cnf,
        ("mutilated", "opb"): mutilated_opb, ("mutilated", "cnf"): mutilated_cnf,
        ("ripple", "opb"): ripple_linear_opb,
    }[(fam, fmt)]
    sys.stdout.write(gen(size))
