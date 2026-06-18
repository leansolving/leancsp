#!/usr/bin/env python3
"""Dump the canonical verified OPB encoding of a CSP expression.

`dump(module, csp_expr)` writes a throwaway Lean file that imports `module`, defines
`dumpCsp := <csp_expr>`, and `#eval`s the variable count and the OPB string of the *generic*
encoder `(cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)` — byte-identical to what
`scripts/gen_cert.sh` and the `csp_unsat_file` theorems use.  Returns `(num_vars, opb_text)`.
"""
from __future__ import annotations

import subprocess
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent

_TEMPLATE = """import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Backends.PB.Serialize
import {module}
open CSP.L2S CSP.L2S.PB {extra_open}
def dumpCsp : IntCSP := {csp_expr}
private def dumpNV : Nat := ((List.finRange (cspSig dumpCsp).nInt).map
  (fun i => (cspSig dumpCsp).width i)).sum + (cspSig dumpCsp).nBool + (cspSig dumpCsp).nAux
#eval IO.println dumpNV
#eval IO.println (toOPBString
  (((cspSig dumpCsp).monotonicity ++ EncConstr.combine (encodeCSP dumpCsp)).toArray.map
    PBConstr.toNatConstr) dumpNV)
"""


def dump(module: str, csp_expr: str, extra_open: str = "", timeout: int = 900):
    """Return (num_vars, opb_text) for the canonical encodeCSP of csp_expr.

    Raises RuntimeError on a Lean error (e.g. an ill-typed expression)."""
    src = _TEMPLATE.format(module=module, extra_open=extra_open, csp_expr=csp_expr)
    f = Path(tempfile.mktemp(suffix=".lean"))
    f.write_text(src)
    try:
        proc = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO,
                              capture_output=True, timeout=timeout)
    finally:
        f.unlink(missing_ok=True)
    out = proc.stdout.decode(errors="replace")
    if proc.returncode != 0 or not out.strip():
        raise RuntimeError(
            f"lean dump failed for `{csp_expr}`:\n{proc.stderr.decode(errors='replace')[:2000]}")
    lines = out.splitlines()
    num_vars = int(lines[0])
    opb_text = "\n".join(lines[1:]) + "\n"
    return num_vars, opb_text


_BATCH_HEAD = """import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Backends.PB.Serialize
import {module}
open CSP.L2S CSP.L2S.PB {extra_open}
def _dump1 (tag : String) (csp : IntCSP) : String :=
  let nv := ((List.finRange (cspSig csp).nInt).map (fun i => (cspSig csp).width i)).sum
            + (cspSig csp).nBool + (cspSig csp).nAux
  s!"@@@ {{tag}} {{nv}}\\n" ++ toOPBString
    (((cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)).toArray.map
      PBConstr.toNatConstr) nv
"""


def dump_batch(module: str, items, extra_open: str = "", timeout: int = 1800):
    """Dump MANY CSPs in ONE warm Lean process (imports loaded once).

    `items` is a list of (tag, csp_expr).  Returns {tag: (num_vars, opb_text)}.  This is the
    key overhead fix: one `lake env lean` startup per *family* instead of one per *instance*.
    """
    body = _BATCH_HEAD.format(module=module, extra_open=extra_open)
    for tag, expr in items:
        body += f'#eval IO.print (_dump1 "{tag}" ({expr}))\n'
    f = Path(tempfile.mktemp(suffix=".lean"))
    f.write_text(body)
    try:
        proc = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO,
                              capture_output=True, timeout=timeout)
    finally:
        f.unlink(missing_ok=True)
    out = proc.stdout.decode(errors="replace")
    if proc.returncode != 0:
        raise RuntimeError(f"batch dump failed:\n{proc.stderr.decode(errors='replace')[:2000]}\n"
                          f"{out[:1000]}")
    # split on the @@@ markers
    result = {}
    cur_tag, cur_nv, cur_lines = None, None, []
    for line in out.splitlines():
        if line.startswith("@@@ "):
            if cur_tag is not None:
                result[cur_tag] = (cur_nv, "\n".join(cur_lines) + "\n")
            _, tag, nv = line.split()
            cur_tag, cur_nv, cur_lines = tag, int(nv), []
        elif cur_tag is not None:
            cur_lines.append(line)
    if cur_tag is not None:
        result[cur_tag] = (cur_nv, "\n".join(cur_lines) + "\n")
    return result


if __name__ == "__main__":
    import sys
    mod, expr = sys.argv[1], sys.argv[2]
    nv, opb = dump(mod, expr)
    hdr = opb.splitlines()[0]
    print(f"numVars={nv}  {hdr}")
