#!/usr/bin/env python3
from __future__ import annotations

import csv
import os
import re
import signal
import subprocess
import sys
from pathlib import Path

import families as F
import harness as H
import lean_dump

REPO = Path(__file__).resolve().parent.parent.parent
RES = REPO / "experiments" / "sbc" / "results"
WORK = REPO / "experiments" / "sbc" / "artifacts" / "largest"
EXE = REPO / ".lake" / "build" / "bin" / "checkbench"
COLUMNS = ["family", "regime", "size_param", "num_vars", "cert_bytes",
           "check_ns", "check_pretty", "num_constraints", "status"]
CHECK_TIMEOUT = 1800     # native checker runs at a few MB/s, so even the 391 MB cert finishes fast
MAX_CHECK_BYTES = 10 ** 9  # safety cap only (nothing here is this large)


def ensure_exe():
    if not EXE.exists():
        print("  building native checker (lake build checkbench) ...", flush=True)
        subprocess.run(["lake", "build", "checkbench"], cwd=REPO, capture_output=True)


def targets(fams):
    best = {}
    for r in csv.DictReader(open(RES / "sbc_scaling.csv")):
        if (r["family"] in fams and r["roundingsat_status"] == "UNSAT" and r["kernel_cert_chars"]):
            c = int(r["kernel_cert_chars"])
            k = (r["family"], r["regime"])
            if k not in best or c > best[k][0]:
                best[k] = (c, int(r["size_param"]))
    return best


def pretty(ns):
    if ns is None:
        return "-"
    us = ns / 1e3
    if us < 1000:
        return f"{us:.0f}us"
    if us < 1e6:
        return f"{us / 1e3:.0f}ms"
    return f"{us / 1e6:.1f}s"


def find_inst(cfg, size):
    return next((it for it in cfg["instances"] if it["nat"] == size), None)


def run_exe(constrs, num_vars, cert, timeout):
    """Run the native `checkbench` exe; (check_ns|None, ok). Kills the process group on timeout."""
    proc = subprocess.Popen([str(EXE), constrs, str(num_vars), cert],
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
    m = re.search(r"NATIVE (\d+) OK (\w+) NCONS (\d+)", out.decode(errors="replace"))
    if proc.returncode != 0 or not m:
        return None, False
    return int(m.group(1)), (m.group(2) == "true")


def measure(fam, regime, size, known_cert, w, fh):
    cfg = F.FAMILIES[fam]
    it = find_inst(cfg, size)
    row = {c: "" for c in COLUMNS}
    row.update(family=fam, regime=regime, size_param=size)
    if it is None:
        row["status"] = "NO-INSTANCE"; w.writerow(row); fh.flush(); return
    if known_cert > MAX_CHECK_BYTES:
        row["cert_bytes"] = known_cert; row["status"] = "TOO-LARGE"
        w.writerow(row); fh.flush(); return
    expr = F.regime_expr(cfg, it, regime)
    WORK.mkdir(parents=True, exist_ok=True)
    constrs = WORK / f"{fam}_{regime}.cs"
    try:
        nv, opb = lean_dump.dump_with_constrs(cfg["module"], expr, str(constrs.resolve()))
    except Exception:
        row["status"] = "DUMP-FAIL"; w.writerow(row); fh.flush(); return
    row["num_vars"] = nv
    opbp = WORK / f"{fam}_{regime}.opb"; opbp.write_text(opb)
    pbp = WORK / f"{fam}_{regime}.pbp"; kernel = WORK / f"{fam}_{regime}_kernel.pbp"
    r, ok = H.run_roundingsat(opbp, pbp)
    if not ok:
        row["status"] = "RSAT-" + r.get("roundingsat_status", "FAIL"); w.writerow(row); fh.flush(); return
    r, ok = H.run_veripb(opbp, pbp, kernel); pbp.unlink(missing_ok=True)
    if not (ok and kernel.exists()):
        row["status"] = "VERIPB-FAIL"; w.writerow(row); fh.flush(); return
    row["cert_bytes"] = kernel.stat().st_size
    ns, cok = run_exe(str(constrs.resolve()), nv, str(kernel.resolve()), CHECK_TIMEOUT)
    kernel.unlink(missing_ok=True); opbp.unlink(missing_ok=True); constrs.unlink(missing_ok=True)
    row["check_ns"] = "" if ns is None else ns
    row["check_pretty"] = pretty(ns)
    row["status"] = "OK" if cok else (f"CHECK->{CHECK_TIMEOUT}s" if ns is None else "CHECK-FALSE")
    w.writerow(row); fh.flush()
    print(f"  [{fam} {regime} n={size}] cert={row['cert_bytes']}B "
          f"check={row['check_pretty']} {row['status']}", flush=True)


def main():
    fams = sys.argv[1:] or list(F.FAMILIES.keys())
    RES.mkdir(parents=True, exist_ok=True)
    ensure_exe()
    tg = targets(set(fams))
    out = RES / "check_largest.csv"
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS)
        w.writeheader()
        for (fam, regime), (c, size) in sorted(tg.items()):
            print(f"=== {fam} {regime}: largest cert n={size} (~{c / 1e6:.1f} MB) ===", flush=True)
            measure(fam, regime, size, c, w, fh)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
