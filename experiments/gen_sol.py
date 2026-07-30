#!/usr/bin/env python3
"""Generate an (untrusted) value-precedence colouring witness for the Schur CSP
`(Schur.schur_csp n c).addConstraint (value_precedence c)`, and commit it under
CSP/L2S/EndToEnd/sols/<out>.sol as a space-separated list of n colours.

SAT-direction analog of experiments/gen_cert.py.  The
MiniZinc model mirrors the value-precedence-extended CSP (0-indexed: variable i is the integer
i+1; triples are i ≤ j with k = i+j+1 < n; "not all equal"; plus the full Law–Lee value
precedence SBC matching `patternHolds`, which implies x[0] = 0).  The witness is untrusted:
`csp_sat_file` re-checks it in the Lean kernel, so a wrong model here only fails to elaborate —
it can never produce an unsound theorem.

Usage: python experiments/gen_sol.py <n> <c> <out> [solver]
  <n>       number of integers {1,…,n}
  <c>       number of colours
  <out>     witness base name, e.g. schur_c2_n4   (-> sols/schur_c2_n4.sol)
  [solver]  MiniZinc solver (default: gecode; use chuffed for the larger instances)

Needs minizinc (on PATH) with the requested solver.
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SOLDIR = REPO / "CSP/L2S/EndToEnd/sols"

MODEL = """int: n = {n};
int: c = {c};
array[0..n-1] of var 0..c-1: x;
% full value-precedence SBC (matches patternHolds; implies x[0] = 0):
constraint forall(j in 0..n-1)( x[j] >= 1 -> exists(i in 0..j-1)(x[i] = x[j] - 1) );
constraint forall(i in 0..n-1, j in i..n-1 where i + j + 1 <= n - 1)(
  not (x[i] = x[j] /\\ x[j] = x[i + j + 1]));
solve satisfy;
output [ show(x[i]) ++ (if i < n - 1 then " " else "" endif) | i in 0..n-1 ];
"""


def main() -> None:
    if len(sys.argv) not in (4, 5):
        sys.exit("usage: python experiments/gen_sol.py <n> <c> <out> [solver]")
    n, c, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    solver = sys.argv[4] if len(sys.argv) == 5 else "gecode"
    SOLDIR.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        mzn = Path(tmp) / f"{out}.mzn"
        mzn.write_text(MODEL.format(n=n, c=c))
        res = subprocess.run(["minizinc", "--solver", solver, str(mzn)],
                             capture_output=True, text=True)
    line = res.stdout.splitlines()[0] if res.stdout.strip() else ""
    if not line or "UNSATISFIABLE" in line:
        sys.exit(f"ERROR: solver {solver} found no colouring for n={n} c={c}")
    sol = SOLDIR / f"{out}.sol"
    sol.write_text(line + "\n")
    print(f"wrote {sol}  ({len(line.split())} colours)")


if __name__ == "__main__":
    main()
