#!/usr/bin/env python3
"""Assert that pbgen.py's OPB output is byte-for-byte identical to the verified
in-Lean *generic* encoder, at every size that has a committed `_unsat` theorem.

This is the guarantee that makes the external-sweep certificate-size numbers
directly comparable to the in-Lean instances: the standalone Python generator
and the Lean pipeline encode the *same formula*.

For each case below, we ask Lean to serialize the canonical generic encoding
`(cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)` via
`toOPBString` (the same dump `scripts/gen_cert.sh` feeds to RoundingSat, and
the formula the one-line `csp_unsat_file` theorems kernel-check) and diff it
against pbgen's output.

Run:  uv run python validate.py        (needs `lake`, from the repo root)
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

import pbgen

REPO = Path(__file__).resolve().parent.parent.parent

PROBLEMS = "CSP.L2S.Backends.PB.Problems"


def generic_expr(csp: str) -> str:
    """The canonical generic encoding of `csp`, mapped to checker constraints."""
    return (f"(((cspSig {csp}).monotonicity ++ EncConstr.combine (encodeCSP {csp}))"
            f".toArray.map PBConstr.toNatConstr)")


# (label, lean_module, csp_expr, extra_open, numVars, python_text)
# NOTE: each generated temp file imports exactly ONE Problems module — the corpus
# modules under Tests/lean/ each define `main`, so importing two Problems wrappers
# backed by different corpus files collides on `main`.
CASES = [
    ("php n=2 (php_3_2)", f"{PROBLEMS}.Pigeonhole",
     "php_3_2", "", 3, pbgen.php_opb(2)),
    ("php n=4 (php_5_4)", f"{PROBLEMS}.Pigeonhole",
     "php_5_4", "", 15, pbgen.php_opb(4)),
    ("php n=6 (php_7_6)", f"{PROBLEMS}.Pigeonhole",
     "php_7_6", "", 35, pbgen.php_opb(6)),
    ("php n=8 (php_9_8)", f"{PROBLEMS}.Pigeonhole",
     "php_9_8", "", 63, pbgen.php_opb(8)),
    ("mutilated k=2 (4x4)", f"{PROBLEMS}.MutilatedChessboard",
     "mutilatedChessboard", "CSP.L2S.PB.MutilatedChessboard",
     20, pbgen.mutilated_opb(2)),
    ("mutilated k=3 (6x6)", f"{PROBLEMS}.MutilatedChessboard6",
     "mutilatedChessboard6", "CSP.L2S.PB.MutilatedChessboard6",
     56, pbgen.mutilated_opb(3)),
    ("oddcycle n=5 (c5_2col)", f"{PROBLEMS}.OddCycle",
     "c5_2col", "", 5, pbgen.oddcycle_opb(5)),
    ("oddcycle n=7 (c7_2col)", f"{PROBLEMS}.OddCycle",
     "c7_2col", "", 7, pbgen.oddcycle_opb(7)),
    ("oddcycle n=9 (c9_2col)", f"{PROBLEMS}.OddCycle",
     "c9_2col", "", 9, pbgen.oddcycle_opb(9)),
]


def lean_dump(module: str, csp: str, extra_open: str, num_vars: int) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir="/tmp",
                                     delete=False) as f:
        out = f"/tmp/_validate_{abs(hash((module, csp)))}.opb"
        f.write(f"import {module}\nimport CSP.L2S.Backends.PB.Serialize\n"
                f"open CSP.L2S CSP.L2S.PB {extra_open}\n"
                f'#eval IO.FS.writeFile "{out}" '
                f"(toOPBString {generic_expr(csp)} {num_vars})\n")
        src = f.name
    subprocess.run(["lake", "env", "lean", src], cwd=REPO, check=True,
                   capture_output=True)
    return Path(out).read_text()


def main() -> int:
    ok = True
    for label, module, csp, extra_open, nv, py in CASES:
        gt = lean_dump(module, csp, extra_open, nv)
        if gt == py:
            print(f"  OK   {label}: byte-identical ({len(py)} bytes)")
        else:
            ok = False
            print(f"  FAIL {label}: differs")
            g, p = gt.splitlines(), py.splitlines()
            for i, (a, b) in enumerate(zip(g, p)):
                if a != b:
                    print(f"       line {i}: lean={a!r}  py={b!r}")
                    break
    print("ALL IDENTICAL" if ok else "VALIDATION FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
