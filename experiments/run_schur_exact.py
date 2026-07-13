#!/usr/bin/env python3
"""Time both Schur verification pipelines (SAT/lower + UNSAT/upper) for S(2)/S(3)/S(4).

For each Schur number S(c) it times, end to end:

  * the **lower bound** (`S(c) ≥ n`) — MiniZinc finds a value-precedence colouring witness
    (`solve_wall_s`), then the Lean kernel re-checks it by `decide` (`lean_check_wall_s`);
  * the **upper bound** (`S(c) < n+1`) — roundingsat solves the value-precedence OPB
    (`solve_wall_s`, machine-independent `rsat_det_time`/`rsat_conflicts`), veripb elaborates
    a certificate (`veripb_wall_s`), and Lean `native_decide` reflectively checks it
    (`lean_check_wall_s`) when the certificate is small enough.

Both directions use the SAME symmetry-breaking constraint (Law–Lee value precedence), proved
equisatisfiable in `CSP/L2S/Proofs/SchurValuePrecedence.lean`, so every measurement maps onto
a CSP-level theorem about the original simple CSP `Schur.schur_sb n c`
(`CSP/L2S/EndToEnd/SchurCertify.lean`).

Reuses experiments/lib/{harness,lean_recheck}.py.  Writes experiments/schur_exact/results/timings.csv;
certificates (incl. the ~98 MB S(4) kernel cert read by CSP/L2S/EndToEnd/Schur4Upper.lean) land in
experiments/schur_exact/artifacts/ (gitignored, regenerable).  One representative run per stage
(no median-of-N) — startup noise dwarfs the cheap stages, and the S(4) solve is too costly to repeat.

Usage: python experiments/run_schur_exact.py
"""
from __future__ import annotations

import csv
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "experiments" / "lib"))
import harness          # noqa: E402
import lean_recheck     # noqa: E402

WORK = REPO / "experiments" / "schur_exact" / "artifacts"
OUT_CSV = REPO / "experiments" / "schur_exact" / "results" / "timings.csv"
SOLDIR = "CSP/L2S/EndToEnd/sols"           # project-root-relative (csp_sat_file reads from CWD)
CERTDIR = REPO / "CSP/L2S/Backends/PB/Problems/certs"
VP_MODULE = "CSP.L2S.Proofs.SchurValuePrecedence"

# Largest certificate (bytes) we will even attempt to native_decide.  S(4)'s ~100 MB cert is
# far past anything the reflective checker can absorb, so it is recorded external-verified.
NATIVE_DECIDE_CAP = 2_000_000

# (colours, lower-bound n, minizinc solver).  Upper bound is at n+1.
INSTANCES = [(2, 4, "gecode"), (3, 13, "gecode"), (4, 44, "chuffed")]

COLUMNS = ["c", "n", "bound", "instance", "solve_tool", "solve_wall_s",
           "rsat_det_time", "rsat_conflicts", "veripb_wall_s",
           "cert_or_witness_bytes", "lean_check_wall_s", "lean_check_kind", "status"]


def vp_expr(n: int, c: int) -> str:
    return f"(Schur.schur_sb {n} {c}).addConstraint (value_precedence {c})"


def mzn_model(n: int, c: int) -> str:
    return (f"int: n = {n};\nint: c = {c};\narray[0..n-1] of var 0..c-1: x;\n"
            "constraint forall(j in 0..n-1)( x[j] >= 1 -> exists(i in 0..j-1)(x[i] = x[j]-1) );\n"
            "constraint forall(i in 0..n-1, j in i..n-1 where i + j + 1 <= n - 1)("
            "not (x[i] = x[j] /\\ x[j] = x[i + j + 1]));\nsolve satisfy;\n"
            'output [ show(x[i]) ++ " " | i in 0..n-1 ];\n')


def dump_opb(n: int, c: int, tag: str) -> tuple[Path, int]:
    """#eval the canonical OPB of the value-precedence instance; return (opb_path, num_vars)."""
    dump = REPO / "CSP/L2S/Backends/PB/Problems" / f"_dump_{tag}.lean"
    dump.write_text(
        "import CSP.L2S.Backends.PB.GenericEncode\nimport CSP.L2S.Backends.PB.Serialize\n"
        f"import {VP_MODULE}\nopen CSP.L2S CSP.L2S.PB\n"
        f"def dumpCsp : IntCSP := {vp_expr(n, c)}\n"
        "private def dumpNV : Nat := ((List.finRange (cspSig dumpCsp).nInt).map "
        "(fun i => (cspSig dumpCsp).width i)).sum + (cspSig dumpCsp).nBool + (cspSig dumpCsp).nAux\n"
        "#eval IO.println dumpNV\n"
        "#eval IO.println (toOPBString (((cspSig dumpCsp).monotonicity ++ "
        "EncConstr.combine (encodeCSP dumpCsp)).toArray.map PBConstr.toNatConstr) dumpNV)\n")
    out = subprocess.run(["lake", "env", "lean", str(dump)], cwd=REPO,
                         capture_output=True, text=True)
    dump.unlink(missing_ok=True)
    lines = out.stdout.splitlines()
    nv = int(lines[0])
    opb = WORK / f"schur_{tag}.opb"
    opb.write_text("\n".join(lines[1:]) + "\n")
    return opb, nv


def sat_check_wall(n: int, c: int, witness_rel: str, base: float) -> float | None:
    """`lake env lean` wall (minus import baseline) of the csp_sat_file kernel-`decide` obligation."""
    f = Path("/tmp/_schur_sat_check.lean")
    f.write_text(
        "import CSP.L2S.Witness\n" f"import {VP_MODULE}\n" "open CSP.L2S\n"
        "set_option maxRecDepth 10000 in\n"
        f'example : ({vp_expr(n, c)}).isSatisfiableInt := csp_sat_file ({vp_expr(n, c)}) "{witness_rel}"\n')
    t0 = time.monotonic()
    proc = subprocess.run(["lake", "env", "lean", str(f)], cwd=REPO, capture_output=True)
    if proc.returncode != 0:
        return None
    return max(0.0, time.monotonic() - t0 - base)


def main() -> None:
    WORK.mkdir(parents=True, exist_ok=True)
    harness.REPEATS = 1   # one representative wall-clock per stage
    rows = []

    # Baselines (import-only `lake env lean` wall) for the two recheck flavours.
    sat_base = lean_recheck._wall_min(  # Witness + VP import baseline
        ["lake", "env", "lean", _write("/tmp/_schur_sat_base.lean",
            "import CSP.L2S.Witness\n" f"import {VP_MODULE}\nopen CSP.L2S\n")], repeats=3)
    unsat_base = lean_recheck.baseline(VP_MODULE, repeats=3)

    for c, n, solver in INSTANCES:
        # ---- SAT / lower bound: MiniZinc solve + kernel decide ----
        print(f"[S({c}) >= {n}] SAT leg ...", flush=True)
        mzn = WORK / f"schur_c{c}_n{n}.mzn"
        mzn.write_text(mzn_model(n, c))
        t, status, out = harness.timed(["minizinc", "--solver", solver, str(mzn)], repeats=1)
        witness_rel = f"{SOLDIR}/schur_c{c}_n{n}.sol"
        wbytes = (REPO / witness_rel).stat().st_size
        chk = sat_check_wall(n, c, witness_rel, sat_base)
        rows.append({"c": c, "n": n, "bound": "lower",
                     "instance": f"schur_{c}_{n}", "solve_tool": f"minizinc-{solver}",
                     "solve_wall_s": harness.fmt(t), "cert_or_witness_bytes": wbytes,
                     "lean_check_wall_s": harness.fmt(chk), "lean_check_kind": "kernel-decide",
                     "status": "SAT" + ("/CHECKED" if chk is not None else "/CHECK-FAIL")})

        # ---- UNSAT / upper bound: roundingsat + veripb + native_decide ----
        m = n + 1
        print(f"[S({c}) < {m}] UNSAT leg ...", flush=True)
        opb, nv = dump_opb(m, c, f"c{c}n{m}")
        pbp = WORK / f"schur_{c}_{m}_vp.pbp"
        kernel = WORK / f"schur_{c}_{m}_vp_kernel.pbp"
        rrow, ok = harness.run_roundingsat(opb, pbp)
        vrow = {}
        cert_bytes, lean_chk, kind, ustatus = "", "", "native_decide", "ROUNDINGSAT-FAIL"
        if ok:
            vrow, vok = harness.run_veripb(opb, pbp, kernel)
            if vok:
                cert_bytes = vrow.get("veripb_proof_bytes", "")
                if int(cert_bytes) <= NATIVE_DECIDE_CAP:
                    cabs = str(CERTDIR / f"schur_{'2_5' if (c,m)==(2,5) else '3_14'}_vp.pbp") \
                        if (c, m) in [(2, 5), (3, 14)] else str(kernel)
                    t_chk, cok = lean_recheck.native_decide_time(
                        VP_MODULE, vp_expr(m, c), nv, cabs, unsat_base, timeout=900)
                    lean_chk = harness.fmt(t_chk)
                    ustatus = "UNSAT/CHECKED" if cok else "UNSAT/CHECK-FAIL"
                else:
                    lean_chk, ustatus = "", "UNSAT/EXTERNAL(cert too large)"
            else:
                ustatus = "VERIPB-FAIL"
        rows.append({"c": c, "n": m, "bound": "upper",
                     "instance": f"schur_{c}_{m}", "solve_tool": "roundingsat",
                     "solve_wall_s": rrow.get("roundingsat_time_s", ""),
                     "rsat_det_time": rrow.get("rsat_det_time", ""),
                     "rsat_conflicts": rrow.get("rsat_conflicts", ""),
                     "veripb_wall_s": vrow.get("veripb_elaborate_time_s", ""),
                     "cert_or_witness_bytes": cert_bytes,
                     "lean_check_wall_s": lean_chk, "lean_check_kind": kind, "status": ustatus})

    OUT_CSV.parent.mkdir(parents=True, exist_ok=True)
    with open(OUT_CSV, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS)
        w.writeheader()
        for r in rows:
            w.writerow({k: r.get(k, "") for k in COLUMNS})
    print(f"\nwrote {OUT_CSV}")
    for r in rows:
        print(f"  S({r['c']}) {r['bound']:5} n={r['n']:<3} {r['status']:30} "
              f"solve={r['solve_wall_s']}s  lean_check={r['lean_check_wall_s']}s")


def _write(path: str, text: str) -> str:
    Path(path).write_text(text)
    return path


if __name__ == "__main__":
    main()
