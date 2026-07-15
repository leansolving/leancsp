#!/usr/bin/env python3
from __future__ import annotations

import os
import re
import shutil
import signal
import statistics
import subprocess
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent
BENCH = REPO / "CSP" / "L2S" / "Backends" / "PB" / "Bench"   # temp reflection modules (under CSP/ so lake checks them)
BENCH_CERTS = BENCH / "certs"                                # csp_unsat_file reads certs module-relative
CHECKBENCH = REPO / ".lake" / "build" / "bin" / "checkbench"  # native compiled checker exe
_TMP = "ChkTmp"       # one-theorem reflection module
_EMPTY = "ChkEmpty"   # imports-only baseline module (nets out fixed per-build overhead)


def ensure_checkbench():
    if not CHECKBENCH.exists():
        subprocess.run(["lake", "build", "checkbench"], cwd=REPO, capture_output=True)


def native_check_time(constrs_path: str, nv: int, cert_path: str, timeout: float = 1800) -> tuple:
    """Native `checkProofBool` runtime via the compiled `checkbench` exe (cert pre-loaded from disk).
    The pure checker-algorithm cost. Returns (check_ns|None, ok)."""
    ensure_checkbench()
    proc = subprocess.Popen([str(CHECKBENCH), str(constrs_path), str(nv), str(cert_path)],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.communicate()
        return None, False
    m = re.search(rb"NATIVE (\d+) OK (\w+) NCONS (\d+)", out)
    if proc.returncode != 0 or not m:
        return None, False
    return int(m.group(1)), (m.group(2) == b"true")


def _write_reflection_module(name: str, fam_module: str, expr: str, nv: int, cert_rel: str):
    BENCH.mkdir(parents=True, exist_ok=True)
    (BENCH / f"{name}.lean").write_text(
        "import CSP.L2S.Backends.PB.GenericEncode\n"
        f"import {fam_module}\n"
        "open CSP.L2S CSP.L2S.PB IntCSP\n"
        f"namespace CSP.L2S.PB.Bench.{name}\n"
        "set_option maxRecDepth 100000 in\n"
        # No heartbeat limit: the wall-clock timeout in module_build_time is the real guard, so a
        # valid cert never spuriously BUILD-FAILs. The default 200k now suffices for every family
        # (csp_unsat's `hbound` is settled by the range-prefix theorems in CSP/L2S/Core.lean rather
        # than re-decided per instance), but large certs are elaborated via `include_str`, which this
        # keeps out of the budget too.
        "set_option maxHeartbeats 0 in\n"
        f"theorem chk : ¬ ({expr}).isSatisfiableInt :=\n"
        f'  csp_unsat_file ({expr}) {nv} "certs/{cert_rel}"\n'
        f"end CSP.L2S.PB.Bench.{name}\n")


def _empty_build_baseline(fam_module: str, cache: dict) -> float | None:
    """`lake build` wall of an imports-only module — the fixed per-module overhead (Mathlib import
    load + olean write) to net out of the theorem build. Cached per import set."""
    if fam_module in cache:
        return cache[fam_module]
    BENCH.mkdir(parents=True, exist_ok=True)
    (BENCH / f"{_EMPTY}.lean").write_text(
        f"import CSP.L2S.Backends.PB.GenericEncode\nimport {fam_module}\n")
    bt, ok = module_build_time(f"CSP.L2S.Backends.PB.Bench.{_EMPTY}", timeout=600)
    (BENCH / f"{_EMPTY}.lean").unlink(missing_ok=True)
    cache[fam_module] = bt if ok else None
    return cache[fam_module]


def pipeline_build_time(fam_module: str, expr: str, nv: int, cert_abspath: str,
                        baseline_cache: dict, timeout: float = 1800) -> tuple:
    """The real in-Lean pipeline cost: emit ONE `csp_unsat_file` reflection theorem and time its
    `lake build` (cert read + addAndCompile + ofReduceBool native eval + kernel accept — native
    when PBLean is precompiled). Returns (net_s|None, gross_s|None, status)."""
    module = f"CSP.L2S.Backends.PB.Bench.{_TMP}"
    base = _empty_build_baseline(fam_module, baseline_cache)
    BENCH_CERTS.mkdir(parents=True, exist_ok=True)
    cert_rel = f"{_TMP}.pbp"
    shutil.copyfile(cert_abspath, BENCH_CERTS / cert_rel)
    _write_reflection_module(_TMP, fam_module, expr, nv, cert_rel)
    try:
        gross, ok = module_build_time(module, timeout=timeout)
    finally:
        (BENCH / f"{_TMP}.lean").unlink(missing_ok=True)
        (BENCH_CERTS / cert_rel).unlink(missing_ok=True)
    if gross is None:
        return None, None, "TIMEOUT"
    if not ok:
        return None, round(gross, 3), "BUILD-FAIL"
    if base is None:
        # The imports-only baseline failed to build, so there is nothing to net against. `gross` is
        # still sound; say so rather than reporting a blank `net` under an "OK" status.
        return None, round(gross, 3), "NO-BASELINE"
    return round(max(0.0, gross - base), 3), round(gross, 3), "OK"


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


def module_build_time(module: str, timeout: float | None = None) -> tuple[float | None, bool]:
    """Time `lake build <module>` after deleting its olean — one warm Lean process that
    ofReduceBool-reflection kernel-checks EVERY theorem in the module (per-module build cost).
    Returns (wall_s, ok): (wall_s, True) on success, (wall_s, False) if the build errored,
    (None, False) on timeout (the process group is killed)."""
    _rmartifacts(module)
    t0 = time.monotonic()
    proc = subprocess.Popen(["lake", "build", module], cwd=REPO,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try:
        proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.communicate()
        return None, False
    return time.monotonic() - t0, proc.returncode == 0


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


def encode_expr(csp: str, num_constraints: int) -> str:
    """A native_decide goal that forces ONLY the in-kernel encoder — it builds the checker-ready
    formula `(cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)` (mapped to checker
    constraints) and reads its constraint count — with no certificate checking.  Compiled
    `Array.map` is strict, so reaching `.size` forces every constraint to be fully evaluated."""
    return (f"(((cspSig ({csp})).monotonicity ++ EncConstr.combine (encodeCSP ({csp}))).toArray.map "
            f"PBConstr.toNatConstr).size = {num_constraints} := by native_decide")


def _time_example(body: str, module: str, base: float, extra_open: str, timeout: int):
    """Time one `lake env lean` elaborating `example : {body}`, minus the import-only baseline.

    One real run: confirms the goal elaborates *and* times it.  We deliberately do NOT re-run for a
    min-of-N estimate — each extra `lake env lean` is ~2.3 s of Lean/Mathlib startup that dwarfs the
    (~0–1 s) native_decide signal; one run keeps the sweep ~3× faster, at ±~0.3 s startup noise."""
    f = Path("/tmp/_sbc_recheck.lean")
    f.write_text(_IMPORTS.format(module=module) + f"open CSP.L2S CSP.L2S.PB {extra_open}\n"
                 f"example : {body}\n")
    t0 = time.monotonic()
    try:
        proc = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO,
                              capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, False
    if proc.returncode != 0:
        return None, False
    return max(0.0, (time.monotonic() - t0) - base), True


def native_decide_time(module: str, csp_expr: str, num_vars: int, cert_abspath: str,
                       base: float, extra_open: str = "", timeout: int = 600):
    """Total recheck-minus-baseline (encoding + checking); (time_s|None, ok)."""
    return _time_example(recheck_expr(csp_expr, num_vars, cert_abspath), module, base,
                         extra_open, timeout)


def encode_time(module: str, csp_expr: str, num_constraints: int,
                base: float, extra_open: str = "", timeout: int = 600):
    """Encoder-only recheck-minus-baseline (no certificate checking); (time_s|None, ok).
    Subtract from native_decide_time to isolate PBLean's verified-checker cost."""
    return _time_example(encode_expr(csp_expr, num_constraints), module, base, extra_open, timeout)


def runtime_split(module: str, csp_expr: str, num_vars: int, cert_abspath: str,
                  base: float, extra_open: str = "", timeout: int = 900):
    """Time the COMPILED encoder vs checker *runtimes* in ONE process, via Lean's own monotonic
    clock — so there is no cross-run startup subtraction and the two phases share one clock.

    Returns (wall_minus_base_s|None, encode_us|None, check_us|None, ok).  `encode_us` builds the
    checker-ready formula `(cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)` (strict
    `Array.map` forces every constraint); `check_us` runs `checkProofBool` — the exact compiled
    function the committed `Lean.ofReduceBool` reflection reduces — on the certificate.  `wall_minus_base_s` is
    the whole `lake env lean`, i.e. ≈ the cost of *compiling* the reflected term (what scales with
    instance size), not the (sub-ms) runtime."""
    body = (
        "#eval show IO Unit from do\n"
        f"  let csp : IntCSP := {csp_expr}\n"
        "  let t0 ← IO.monoNanosNow\n"
        "  let cs := (((cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)).toArray.map"
        " PBConstr.toNatConstr)\n"
        "  let n := cs.size\n"
        "  let t1 ← IO.monoNanosNow\n"
        f'  let ok := VeriPB.Reflect.checkProofBool cs {num_vars} (include_str "{cert_abspath}")\n'
        "  let t2 ← IO.monoNanosNow\n"
        '  IO.println s!"SPLIT ENC {(t1 - t0) / 1000} CHK {(t2 - t1) / 1000} N {n} OK {ok}"\n')
    f = Path("/tmp/_sbc_split.lean")
    f.write_text(_IMPORTS.format(module=module) + f"open CSP.L2S CSP.L2S.PB {extra_open}\n" + body)
    t0 = time.monotonic()
    try:
        proc = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO,
                              capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, None, None, False
    wall = time.monotonic() - t0
    m = re.search(r"SPLIT ENC (\d+) CHK (\d+) N \d+ OK (\w+)", proc.stdout.decode(errors="replace"))
    if proc.returncode != 0 or not m or m.group(3) != "true":
        return None, None, None, False
    return max(0.0, wall - base), int(m.group(1)), int(m.group(2)), True

