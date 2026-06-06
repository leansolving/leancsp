#!/usr/bin/env python3
"""Assert that pbgen.py's OPB output is byte-for-byte identical to the verified
in-Lean encoder, at every size that has a committed `_unsat` theorem.

This is the guarantee that makes the external-sweep certificate-size numbers
directly comparable to the in-Lean instances: the standalone Python generator
and the Lean pipeline encode the *same formula*.

For each (module, lean-expression, numVars, python-call) below, we ask Lean to
serialize the committed encoding via `toOPBString` (the same serializer the
checked theorems use) and diff it against pbgen's output.

Run:  uv run python validate.py        (needs `lake`, from the repo root)
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

import pbgen

REPO = Path(__file__).resolve().parent.parent.parent

# (label, lean_import, lean_opb_expr, numVars, python_text)
CASES = [
    ("php n=2 (php_3_2)", "CSP.L2S.Backends.PB.Pigeonhole",
     "Pigeonhole.phpEncoded.toArray.map PBConstr.toNatConstr", 3, pbgen.php_opb(2)),
    ("php n=4 (php_5_4)", "CSP.L2S.Backends.PB.Pigeonhole",
     "Pigeonhole.php5Encoded.toArray.map PBConstr.toNatConstr", 15, pbgen.php_opb(4)),
    ("mutilated k=2 (4x4)", "CSP.L2S.Backends.PB.MutilatedChessboard",
     "(encodeLinear MutilatedChessboard.mcSig MutilatedChessboard.mcLin)"
     ".toArray.map PBConstr.toNatConstr", 20, pbgen.mutilated_opb(2)),
]


def lean_dump(module: str, expr: str, num_vars: int) -> str:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir="/tmp",
                                     delete=False) as f:
        out = f"/tmp/_validate_{abs(hash((module, expr)))}.opb"
        f.write(f"import {module}\nimport CSP.L2S.Backends.PB.Serialize\n"
                f"open CSP.L2S.PB\n"
                f'#eval IO.FS.writeFile "{out}" (toOPBString ({expr}) {num_vars})\n')
        src = f.name
    subprocess.run(["lake", "env", "lean", src], cwd=REPO, check=True,
                   capture_output=True)
    return Path(out).read_text()


def main() -> int:
    ok = True
    for label, module, expr, nv, py in CASES:
        gt = lean_dump(module, expr, nv)
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
