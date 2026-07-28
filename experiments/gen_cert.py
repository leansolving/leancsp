#!/usr/bin/env python3
"""Regenerate a VeriPB kernel certificate for one CSP against the *canonical* generic
encoder (`encodeCSP`), and commit it under CSP/L2S/Backends/PB/Problems/certs/<out>.pbp.

Reuses experiments/lib/harness.py for the roundingsat + veripb runners, so tool
resolution and timeouts match the rest of the experiments.

Usage: python experiments/gen_cert.py <Module> <cspExpr> <out>
  <Module>   module defining the CSP, e.g. CSP.L2S.Backends.PB.Problems.Sudoku
  <cspExpr>  a Lean term of type IntCSP, e.g. sudoku_4
  <out>      certificate base name, e.g. sudoku_4   (-> Problems/certs/sudoku_4.pbp)

Prints `numVars=<N>` — the OPB `#variable=` count to pass to `csp_unsat_file`.
Needs roundingsat (ROUNDINGSAT env or on PATH) and veripb (on PATH).
"""
from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "experiments" / "lib"))
import harness          # noqa: E402

CERTDIR = REPO / "CSP/L2S/Backends/PB/Problems/certs"


def dump_opb(module: str, csp_expr: str, opb_path: Path) -> int:
    """`#eval` the canonical OPB of `csp_expr`; write it to `opb_path`, return num_vars.

    Mirrors `(cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)` exactly, so the
    certificate is checked against the *same* formula the committed theorem reflects.
    """
    dump = REPO / "CSP/L2S/Backends/PB/Problems" / "_dump.lean"   # gitignored
    dump.write_text(
        "import CSP.L2S.Backends.PB.GenericEncode\nimport CSP.L2S.Backends.PB.Serialize\n"
        f"import {module}\nopen CSP.L2S CSP.L2S.PB\n"
        f"def dumpCsp : IntCSP := {csp_expr}\n"
        "private def dumpNV : Nat := ((List.finRange (cspSig dumpCsp).nInt).map "
        "(fun i => (cspSig dumpCsp).width i)).sum + (cspSig dumpCsp).nBool + (cspSig dumpCsp).nAux\n"
        "#eval IO.println dumpNV\n"
        "#eval IO.println (toOPBString (((cspSig dumpCsp).monotonicity ++ "
        "EncConstr.combine (encodeCSP dumpCsp)).toArray.map PBConstr.toNatConstr) dumpNV)\n")
    try:
        out = subprocess.run(["lake", "env", "lean", str(dump)], cwd=REPO,
                             capture_output=True, text=True)
    finally:
        dump.unlink(missing_ok=True)
    if out.returncode != 0:
        sys.exit(f"ERROR: lean dump failed for {csp_expr}\n{out.stderr}")
    lines = out.stdout.splitlines()
    nv = int(lines[0])
    opb_path.write_text("\n".join(lines[1:]) + "\n")
    return nv


def main() -> None:
    if len(sys.argv) != 4:
        sys.exit("usage: python experiments/gen_cert.py <Module> <cspExpr> <out>")
    module, csp_expr, out = sys.argv[1], sys.argv[2], sys.argv[3]
    CERTDIR.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory() as tmp:
        opb = Path(tmp) / f"{out}.opb"
        pbp = Path(tmp) / f"{out}.pbp"
        cert = CERTDIR / f"{out}.pbp"
        nv = dump_opb(module, csp_expr, opb)
        rrow, ok = harness.run_roundingsat(opb, pbp)
        if not ok:
            sys.exit(f"ERROR: roundingsat did not report UNSATISFIABLE for {csp_expr} "
                     f"({rrow.get('roundingsat_status', '?')})")
        _, vok = harness.run_veripb(opb, pbp, cert)
        if not vok:
            sys.exit(f"ERROR: veripb failed to verify {csp_expr}")
    print(f"numVars={nv}  ->  {cert}")


if __name__ == "__main__":
    main()
