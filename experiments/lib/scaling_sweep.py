#!/usr/bin/env python3
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

# roundingsat is found via $ROUNDINGSAT (a path to the binary) or on PATH — no hardcoded location.
RSAT = os.environ.get("ROUNDINGSAT") or shutil.which("roundingsat")
if not RSAT or not Path(RSAT).exists():
    sys.exit("ERROR: roundingsat not found — set $ROUNDINGSAT to its path or put it on PATH")


def have(tool: str) -> bool:
    return shutil.which(tool) is not None

HERE = Path(__file__).resolve().parent            # experiments/lib
REPO = HERE.parent.parent                         # repo root
RESULTS = REPO / "experiments" / "scaling" / "results"           # committed CSVs
WORK = REPO / "experiments" / "scaling" / "artifacts" / "_work"  # scratch (git-excluded)
CSV_PATH = RESULTS / "scaling.csv"

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
        # `status` reports the run, not the verdict: it is "ok" on a non-timeout failure, which
        # verbatim put "ok" in a proof-length column. Mark it as harness.run_veripb does.
        row["veripb_proof_lines"] = status if status == "TIMEOUT" else "FAIL"
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
def sweep_family(family, writer, fh, limit=None):
    cfg = SWEEP[family]
    # `limit` keeps only the smallest few sizes (smoke test)
    pb_sizes = cfg["pb"] if limit is None else cfg["pb"][:limit]
    drat_sizes = cfg["drat"] if limit is None else cfg["drat"][:limit]
    rows = {}
    # PB sweep (auto-stop on timeout).
    pb_ok = True
    for size in pb_sizes:
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
    for size in drat_sizes:
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


def merge_csvs(families=("php", "mutilated", "oddcycle"), suffix=""):
    """Combine the per-family scaling_<family>.csv into scaling.csv (both under RESULTS)."""
    rows = []
    for fam in families:
        p = RESULTS / f"scaling_{fam}{suffix}.csv"
        if p.exists():
            with open(p, newline="") as fh:
                rows.extend(list(csv.DictReader(fh)))
    out = RESULTS / f"scaling{suffix}.csv"
    with open(out, "w", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=COLUMNS)
        writer.writeheader()
        for r in rows:
            writer.writerow(r)
    print(f"Merged {len(rows)} rows -> {out}")


def main():
    argv = sys.argv[1:]
    smoke = "--smoke" in argv                          # only the 2 smallest sizes per family
    families = [a for a in argv if not a.startswith("-")] or ["php", "mutilated", "oddcycle"]
    if families == ["merge"]:
        merge_csvs()
        return
    suffix = ".smoke" if smoke else ""
    limit = 2 if smoke else None
    RESULTS.mkdir(parents=True, exist_ok=True)
    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir(parents=True)
    for fam in families:
        print(f"\n===== {fam} =====", flush=True)
        out = RESULTS / f"scaling_{fam}{suffix}.csv"
        with open(out, "w", newline="") as fh:
            writer = csv.DictWriter(fh, fieldnames=COLUMNS)
            writer.writeheader()
            sweep_family(fam, writer, fh, limit)
        print(f"Wrote {out}")
    shutil.rmtree(WORK, ignore_errors=True)
    merge_csvs(families, suffix)


if __name__ == "__main__":
    main()
