#!/usr/bin/env python3
from __future__ import annotations

import os
import re
import signal
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
    ofReduceBool-reflection kernel-checks EVERY theorem in the module (per-family build cost)."""
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


def check_file_runtime(module: str, csp_expr: str, num_vars: int, cert_abspath: str,
                       extra_open: str = "", timeout: int = 600):
    """Time ONE `checkProofBool` on a certificate read at RUNTIME via `IO.FS.readFile`.

    Unlike `runtime_split` (which embeds the cert with `include_str`, so a 100s-of-MB cert would
    have to be compiled as a string literal), this reads the cert at runtime — so arbitrarily large
    certificates can be timed.  The encoder-built array `cs` and the file read are forced *before*
    t0; `checkProofBool`'s result is forced (an executed `if` branch) *before* t1, so the measured
    span is exactly the checker, not thunk creation.  Returns
    (check_ns|None, ok, num_constraints|None, proof_chars|None); check_ns is None on timeout/OOM.

    On timeout the whole process group is killed (a bare `subprocess` timeout kills only `lake`,
    orphaning the `lean` grandchild)."""
    body = (
        "#eval show IO Unit from do\n"
        f"  let csp : IntCSP := {csp_expr}\n"
        "  let cs := (((cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)).toArray.map"
        " PBConstr.toNatConstr)\n"
        "  let ncons := cs.size\n"                       # force the encoder
        f'  let proof ← IO.FS.readFile "{cert_abspath}"\n'
        "  let plen := proof.length\n"                    # force the whole cert into memory
        "  let t0 ← IO.monoNanosNow\n"
        f"  let ok := VeriPB.Reflect.checkProofBool cs {num_vars} proof\n"
        # force `ok` inside the timed region: `throw` on the false branch is a side effect the
        # compiler cannot eliminate (identical branches would be DCE'd, leaving `ok` unevaluated).
        '  if ok then pure () else throw (IO.userError "CHECK-FALSE")\n'
        "  let t1 ← IO.monoNanosNow\n"
        '  IO.println s!"CHECKFILE {t1 - t0} OK {ok} NCONS {ncons} PLEN {plen}"\n')
    f = Path("/tmp/_check_largest.lean")
    f.write_text(_IMPORTS.format(module=module) + f"open CSP.L2S CSP.L2S.PB {extra_open}\n" + body)
    proc = subprocess.Popen(["lake", "env", "lean", str(f)], cwd=REPO,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, _ = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.communicate()
        return None, False, None, None
    m = re.search(r"CHECKFILE (\d+) OK (\w+) NCONS (\d+) PLEN (\d+)", out.decode(errors="replace"))
    if proc.returncode != 0 or not m:
        return None, False, None, None
    return int(m.group(1)), (m.group(2) == "true"), int(m.group(3)), int(m.group(4))
