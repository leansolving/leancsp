#!/usr/bin/env python3
"""Driver for the verified-PB scaling study.

Sweeps three families across size ranges, running two pipelines per instance:

  PB  (cutting-planes, verified): OPB -> roundingsat -> .pbp proof log
                                  -> veripb --elaborate -> kernel proof
  DRAT (resolution, for contrast): DIMACS CNF -> cadical (DRAT) -> drat-trim

The two resolution-hard families (pigeonhole, mutilated chessboard) make the
resolution proof blow up; the odd-cycle family is the easy non-separation
baseline where BOTH proofs stay small (it runs DRAT too, as the control).

All wall-times are the median of up to 3 runs (a single run is used once a run
exceeds `SLOW_THRESHOLD`, to keep the sweep near the exponential wall tractable).
Each solver call has a hard `TIMEOUT`.  A pipeline auto-stops at the first size
that times out.  Results are appended to results/scaling.csv as they complete.

Usage:
  uv run python run_scaling.py            # full sweep (all families)
  uv run python run_scaling.py php        # one family
  uv run python run_scaling.py php mutilated
roundingsat is taken from $ROUNDINGSAT (falling back to the local-build default,
then PATH).  Missing DRAT-side tools degrade gracefully: a missing SAT solver
skips that leg with sat_status=TOOL-MISSING; a missing drat-trim still records
the proof size and marks drat_trim_status=TOOL-MISSING.
The OPB encoding is byte-for-byte identical to the verified in-Lean generic
encoder, `(cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)`
(asserted by validate.py); see docs/SCALING.md.
"""

from __future__ import annotations

import csv
import os
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

import pbgen

# ---- configuration --------------------------------------------------------- #
TIMEOUT = 600           # seconds, hard per-solver-call limit
REPEATS = 3             # median-of-N for wall-times
SLOW_THRESHOLD = 90     # once a run exceeds this, stop repeating (use 1 sample)

# roundingsat is typically a local build, not on PATH (same default as gen_cert.sh)
_RSAT_DEFAULT = "/home/pablo/projects/roundingsat/build/roundingsat"
RSAT = os.environ.get("ROUNDINGSAT", _RSAT_DEFAULT)
if not Path(RSAT).exists():
    RSAT = shutil.which("roundingsat") or sys.exit(
        f"ERROR: roundingsat not found at {_RSAT_DEFAULT} or on PATH "
        "(set ROUNDINGSAT)")


def have(tool: str) -> bool:
    return shutil.which(tool) is not None

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
WORK = REPO / "results" / "_work"          # scratch (git-excluded); big files deleted
CSV_PATH = REPO / "results" / "scaling.csv"
ENV_PATH = REPO / "results" / "scaling_env.txt"

# Size ranges.  PB sweeps wider (polynomial); DRAT auto-stops at the wall.
# Odd cycle is the easy baseline: both pipelines stay small, so it sweeps far and
# runs DRAT throughout (n is the number of vertices, always odd).
SWEEP = {
    "php":       {"pb": list(range(2, 21)),  "drat": list(range(2, 16))},
    "mutilated": {"pb": [2, 3, 4, 5, 6, 7, 8], "drat": [2, 3, 4, 5, 6, 7]},
    "oddcycle":  {"pb": [3, 5, 7, 9, 11, 15, 21, 31, 51, 75, 101, 151, 201, 301, 501, 751, 1001],
                  "drat": [3, 5, 7, 9, 11, 15, 21, 31, 51, 75, 101, 151, 201, 301, 501, 751, 1001]},
}

COLUMNS = [
    "family", "size_param",
    "pb_vars", "pb_constraints", "opb_bytes",
    "roundingsat_time_s", "roundingsat_status",
    "rsat_log_lines", "rsat_log_bytes",
    "veripb_proof_lines", "veripb_proof_bytes", "veripb_elaborate_time_s",
    "kernel_cert_chars",
    "native_decide_time_s", "module_build_time_s",   # in-Lean checkpoints only
    "cnf_clauses", "sat_solver", "sat_time_s", "sat_status",
    "drat_lines", "drat_bytes", "drat_trim_time_s", "drat_trim_status",
]


# ---- timing helpers -------------------------------------------------------- #
def timed(cmd, timeout=TIMEOUT, repeats=REPEATS, stdout_path=None):
    """Run `cmd` up to `repeats` times; return (median_time | None, status, last_stdout).

    status is 'ok' on a normal exit, 'TIMEOUT' if any run hit the limit.
    On the slow path (a run > SLOW_THRESHOLD) only one sample is taken.
    If stdout_path is given, the last run's stdout is redirected there.
    """
    times, last_out = [], ""
    for _ in range(repeats):
        t0 = time.monotonic()
        try:
            if stdout_path:
                with open(stdout_path, "wb") as fh:
                    proc = subprocess.run(cmd, stdout=fh, stderr=subprocess.PIPE,
                                          timeout=timeout)
                last_out = proc.stderr.decode(errors="replace")
            else:
                proc = subprocess.run(cmd, capture_output=True, timeout=timeout)
                last_out = proc.stdout.decode(errors="replace") + \
                    proc.stderr.decode(errors="replace")
        except subprocess.TimeoutExpired:
            return None, "TIMEOUT", ""
        dt = time.monotonic() - t0
        times.append(dt)
        if dt > SLOW_THRESHOLD:
            break
    return statistics.median(times), "ok", last_out


def file_lines_bytes(path):
    if not os.path.exists(path):
        return 0, 0
    b = os.path.getsize(path)
    with open(path, "rb") as fh:
        n = sum(1 for _ in fh)
    return n, b


# ---- per-instance pipelines ------------------------------------------------ #
def run_pb(family, size, row):
    """PB pipeline: OPB -> roundingsat -> veripb --elaborate.  Returns ok?."""
    opb = WORK / f"{family}_{size}.opb"
    pbp = WORK / f"{family}_{size}.pbp"          # roundingsat proof log
    ker = WORK / f"{family}_{size}.kernel.pbp"   # veripb elaborated kernel proof
    text = {"php": pbgen.php_opb, "mutilated": pbgen.mutilated_opb,
            "oddcycle": pbgen.oddcycle_opb}[family]
    opb.write_text(text(size))

    # header: * #variable= V #constraint= C ...
    hdr = opb.read_text().splitlines()[0].split()
    row["pb_vars"] = int(hdr[hdr.index("#variable=") + 1])
    row["pb_constraints"] = int(hdr[hdr.index("#constraint=") + 1])
    row["opb_bytes"] = opb.stat().st_size

    t, status, out = timed([RSAT, str(opb), f"--proof-log={pbp}"])
    row["roundingsat_time_s"] = fmt(t)
    if status == "TIMEOUT" or "s UNSATISFIABLE" not in out:
        row["roundingsat_status"] = status if status == "TIMEOUT" else "NOT-UNSAT"
        return False
    row["roundingsat_status"] = "UNSAT"
    rl, rb = file_lines_bytes(pbp)
    row["rsat_log_lines"], row["rsat_log_bytes"] = rl, rb

    t, status, out = timed(["veripb", "--elaborate", str(ker), str(opb), str(pbp)])
    row["veripb_elaborate_time_s"] = fmt(t)
    if status == "TIMEOUT" or "s VERIFIED UNSATISFIABLE" not in out:
        row["veripb_proof_lines"] = status
        pbp.unlink(missing_ok=True)
        return False
    kl, kb = file_lines_bytes(ker)
    row["veripb_proof_lines"], row["veripb_proof_bytes"] = kl, kb
    row["kernel_cert_chars"] = len(ker.read_text())
    pbp.unlink(missing_ok=True)          # proof log can be large; size already recorded
    ker.unlink(missing_ok=True)
    return True


def run_drat(family, size, row, solver="cadical"):
    """DRAT pipeline: CNF -> cadical (DRAT) -> drat-trim.  Returns ok?.

    Missing tools degrade gracefully: no solver -> the leg is skipped with
    `sat_status = TOOL-MISSING`; no drat-trim -> the proof is still produced and
    measured, only the trim check is marked TOOL-MISSING.
    """
    row["sat_solver"] = solver
    if not have(solver):
        row["sat_status"] = "TOOL-MISSING"
        return False
    cnf = WORK / f"{family}_{size}.cnf"
    drat = WORK / f"{family}_{size}.drat"
    text = {"php": pbgen.php_cnf, "mutilated": pbgen.mutilated_cnf,
            "oddcycle": pbgen.oddcycle_cnf}[family]
    cnf.write_text(text(size))
    row["cnf_clauses"] = int(cnf.read_text().splitlines()[0].split()[3])

    cmd = ([solver, str(cnf), str(drat), "--no-binary"] if solver == "cadical"
           else [solver, str(cnf), str(drat)])     # kissat emits text DRAT by default
    t, status, out = timed(cmd)
    row["sat_time_s"] = fmt(t)
    if status == "TIMEOUT":
        row["sat_status"] = "TIMEOUT"
        cnf.unlink(missing_ok=True); drat.unlink(missing_ok=True)
        return False
    if "s UNSATISFIABLE" not in out:
        row["sat_status"] = "NOT-UNSAT"
        cnf.unlink(missing_ok=True); drat.unlink(missing_ok=True)
        return False
    row["sat_status"] = "UNSAT"
    dl, db = file_lines_bytes(drat)
    row["drat_lines"], row["drat_bytes"] = dl, db

    if not have("drat-trim"):
        row["drat_trim_status"] = "TOOL-MISSING"
        cnf.unlink(missing_ok=True); drat.unlink(missing_ok=True)
        return True
    t, status, out = timed(["drat-trim", str(cnf), str(drat)])
    row["drat_trim_time_s"] = fmt(t)
    row["drat_trim_status"] = ("VERIFIED" if "s VERIFIED" in out
                               else ("TIMEOUT" if status == "TIMEOUT" else "FAIL"))
    cnf.unlink(missing_ok=True); drat.unlink(missing_ok=True)
    return True


def fmt(t):
    return "" if t is None else f"{t:.4f}"


# ---- sweep orchestration --------------------------------------------------- #
def sweep_family(family, writer, fh):
    cfg = SWEEP[family]
    rows = {}
    # PB sweep (auto-stop on timeout).
    pb_ok = True
    for size in cfg["pb"]:
        if not pb_ok:
            break
        row = {c: "" for c in COLUMNS}
        row["family"], row["size_param"] = family, size
        print(f"[{family} n={size}] PB ...", flush=True)
        ok = run_pb(family, size, row)
        rows[size] = row
        print(f"    vars={row['pb_vars']} cons={row['pb_constraints']} "
              f"rsat={row['roundingsat_time_s']}s({row['roundingsat_status']}) "
              f"veripb={row['veripb_elaborate_time_s']}s cert={row['kernel_cert_chars']}ch",
              flush=True)
        if not ok and row["roundingsat_status"] in ("TIMEOUT",):
            pb_ok = False
    # DRAT sweep (auto-stop on timeout).
    drat_ok = True
    for size in cfg["drat"]:
        if not drat_ok:
            break
        row = rows.get(size) or {c: "" for c in COLUMNS}
        row["family"], row["size_param"] = family, size
        print(f"[{family} n={size}] DRAT ...", flush=True)
        ok = run_drat(family, size, row)
        rows[size] = row
        print(f"    clauses={row['cnf_clauses']} "
              f"sat={row['sat_time_s']}s({row['sat_status']}) "
              f"drat={row['drat_bytes']}B trim={row['drat_trim_time_s']}s",
              flush=True)
        if row["sat_status"] in ("TIMEOUT", "TOOL-MISSING"):
            drat_ok = False
    # emit rows in size order
    for size in sorted(rows):
        writer.writerow(rows[size])
        fh.flush()


def write_env():
    def cap(cmd):
        try:
            return subprocess.run(cmd, capture_output=True, timeout=20
                                  ).stdout.decode(errors="replace").strip()
        except Exception:
            return "(unavailable)"

    def version(tool, *flags):
        if not have(tool):
            return "(not installed)"
        out = cap([tool, *flags])
        return out.splitlines()[-1] if out else "(unavailable)"

    if sys.platform == "darwin":
        cpu = (f"{cap(['sysctl', '-n', 'machdep.cpu.brand_string'])}, "
               f"{cap(['sysctl', '-n', 'hw.ncpu'])} cores")
    else:
        model = "(unknown cpu)"
        for line in Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                model = line.split(":", 1)[1].strip()
                break
        cpu = f"{model}, {os.cpu_count()} cores"
    # roundingsat is a local build: report its path and, if the checkout has git
    # history, its revision (build/ layout -> checkout is two levels up).
    rsat_rev = subprocess.run(
        ["git", "-C", str(Path(RSAT).parent.parent), "rev-parse", "--short", "HEAD"],
        capture_output=True).stdout.decode().strip() or "(unknown rev)"
    lines = [
        "Scaling-study environment",
        "=========================",
        f"machine            : {cap(['uname', '-mnsr'])}",
        f"cpu                : {cpu}",
        f"lean-toolchain     : {(REPO / 'lean-toolchain').read_text().strip()}",
        f"roundingsat        : git {rsat_rev} ({RSAT})",
        f"veripb             : {version('veripb', '--version')}",
        f"cadical            : {version('cadical', '--version')}",
        f"kissat             : {version('kissat', '--version')}",
        f"drat-trim          : {shutil.which('drat-trim') or '(not installed)'}"
        " (no version flag)",
        f"timeout            : {TIMEOUT}s per call; median of up to {REPEATS} runs",
        "mathlib cache       : lake exe cache get (unpacked oleans)",
    ]
    ENV_PATH.write_text("\n".join(lines) + "\n")
    print("\n".join(lines))


def merge_csvs():
    """Combine all results/scaling_<family>.csv into results/scaling.csv."""
    rows = []
    for fam in ("php", "mutilated", "oddcycle"):
        p = REPO / "results" / f"scaling_{fam}.csv"
        if p.exists():
            with open(p, newline="") as fh:
                rows.extend(list(csv.DictReader(fh)))
    with open(CSV_PATH, "w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=COLUMNS)
        writer.writeheader()
        for r in rows:
            writer.writerow(r)
    print(f"Merged {len(rows)} rows -> {CSV_PATH}")


def main():
    families = sys.argv[1:] or ["php", "mutilated", "oddcycle"]
    if families == ["merge"]:
        merge_csvs()
        return
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir(parents=True)
    write_env()
    for fam in families:
        print(f"\n===== {fam} =====", flush=True)
        out = REPO / "results" / f"scaling_{fam}.csv"
        with open(out, "w", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=COLUMNS)
            writer.writeheader()
            sweep_family(fam, writer, fh)
        print(f"Wrote {out}")
    shutil.rmtree(WORK, ignore_errors=True)
    merge_csvs()


if __name__ == "__main__":
    main()
