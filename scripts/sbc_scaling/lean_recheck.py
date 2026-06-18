#!/usr/bin/env python3
"""In-Lean native_decide recheck timing for the SBC bench instances.

Adapted from scripts/scaling/lean_timing.py: times `lake env lean` re-elaborating the
certificate-soundness obligation of `csp_unsat_file <csp> <nv> <cert>` (PBLean's verified checker
run via native_decide on the committed cert), minus an import-only baseline for the same module.
Works for any csp expression + cert path.
"""
from __future__ import annotations

import statistics
import subprocess
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent


def recheck_expr(csp: str, num_vars: int, cert_abspath: str) -> str:
    return (f"VeriPB.Reflect.formulaUnsat (((cspSig ({csp})).monotonicity ++ "
            f"EncConstr.combine (encodeCSP ({csp}))).toArray.map PBConstr.toNatConstr) := "
            f"VeriPB.Reflect.checkProof_sound _ {num_vars} "
            f'(include_str "{cert_abspath}") (by native_decide)')


def _rmartifacts(module: str):
    """Delete a module's build artifacts so `lake build` actually re-runs native_decide
    (lake content-hashes, so `touch` is a no-op)."""
    rel = module.removeprefix("CSP.").replace(".", "/")
    for suf in (".olean", ".olean.hash", ".trace", ".ilean.hash"):
        (REPO / f".lake/build/lib/lean/CSP/{rel}{suf}").unlink(missing_ok=True)
    (REPO / f".lake/build/ir/CSP/{rel}.c.hash").unlink(missing_ok=True)


def module_build_time(module: str) -> float:
    """Time `lake build <module>` after deleting its olean — one warm Lean process that
    native_decide-checks EVERY theorem in the module (the real per-family verification cost)."""
    _rmartifacts(module)
    t0 = time.monotonic()
    subprocess.run(["lake", "build", module], cwd=REPO, capture_output=True)
    return time.monotonic() - t0


def _wall(cmd, repeats=1):
    ts = []
    for _ in range(repeats):
        t0 = time.monotonic()
        subprocess.run(cmd, cwd=REPO, capture_output=True)
        ts.append(time.monotonic() - t0)
    return statistics.median(ts)


def _wall_min(cmd, repeats=5):
    # fixed cost + positive noise ⇒ the minimum is the best estimator
    return min(_wall(cmd, 1) for _ in range(repeats))


_IMPORTS = "import CSP.L2S.Backends.PB.GenericEncode\nimport {module}\n"


def baseline(module: str, extra_open: str = "", repeats=5) -> float:
    f = Path("/tmp/_sbc_baseline.lean")
    f.write_text(_IMPORTS.format(module=module) + f"open CSP.L2S CSP.L2S.PB {extra_open}\n")
    return _wall_min(["lake", "env", "lean", str(f)], repeats)


def native_decide_time(module: str, csp_expr: str, num_vars: int, cert_abspath: str,
                       base: float, extra_open: str = "", timeout: int = 600):
    """recheck-minus-baseline; returns (time_s|None, ok). None+False on a Lean failure/timeout."""
    f = Path("/tmp/_sbc_recheck.lean")
    f.write_text(_IMPORTS.format(module=module) + f"open CSP.L2S CSP.L2S.PB {extra_open}\n"
                 f"example : {recheck_expr(csp_expr, num_vars, cert_abspath)}\n")
    # one real run: confirms the cert elaborates *and* times it.  We deliberately do NOT
    # re-run for a min-of-N estimate — each extra `lake env lean` is ~2.3 s of Lean/Mathlib
    # startup that dwarfs the (~0–1 s) native_decide signal; one run keeps the sweep ~3× faster.
    # native_decide_time_s therefore carries ±~0.3 s startup noise (fine for the scaling trend).
    t0 = time.monotonic()
    try:
        proc = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO,
                              capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, False
    if proc.returncode != 0:
        return None, False
    return max(0.0, (time.monotonic() - t0) - base), True
