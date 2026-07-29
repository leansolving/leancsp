#!/usr/bin/env python3
from __future__ import annotations

import os
import re
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent.parent

TIMEOUT = 600          # hard per-solver-call limit (s)
REPEATS = 3            # median-of-N wall-times
SLOW_THRESHOLD = 60    # once a run exceeds this, stop repeating

# roundingsat is found via $ROUNDINGSAT (a path to the binary) or on PATH — no hardcoded location.
RSAT = os.environ.get("ROUNDINGSAT") or shutil.which("roundingsat")
if not RSAT or not Path(RSAT).exists():
    sys.exit("ERROR: roundingsat not found — set $ROUNDINGSAT to its path or put it on PATH")


def have(tool: str) -> bool:
    return shutil.which(tool) is not None


def fmt(t):
    return "" if t is None else f"{t:.4f}"


def file_lines_bytes(path):
    if not os.path.exists(path):
        return 0, 0
    b = os.path.getsize(path)
    with open(path, "rb") as fh:
        n = sum(1 for _ in fh)
    return n, b


def timed(cmd, timeout=TIMEOUT, repeats=REPEATS, stdout_path=None):
    """Run cmd up to `repeats` times; return (median_time|None, status, last_stdout)."""
    times, last_out = [], ""
    for _ in range(repeats):
        t0 = time.monotonic()
        try:
            if stdout_path:
                with open(stdout_path, "wb") as fh:
                    proc = subprocess.run(cmd, stdout=fh, stderr=subprocess.PIPE, timeout=timeout)
                last_out = proc.stderr.decode(errors="replace")
            else:
                proc = subprocess.run(cmd, capture_output=True, timeout=timeout)
                last_out = proc.stdout.decode(errors="replace") + proc.stderr.decode(errors="replace")
        except subprocess.TimeoutExpired:
            return None, "TIMEOUT", ""
        dt = time.monotonic() - t0
        times.append(dt)
        if dt > SLOW_THRESHOLD:
            break
    return statistics.median(times), "ok", last_out


def _stat(out, pattern):
    m = re.search(pattern, out)
    return m.group(1) if m else ""


def parse_rsat(out: str) -> dict:
    """Extract roundingsat's deterministic-time + search-effort counters."""
    return {
        "rsat_det_time": _stat(out, r"c deterministic time (\d+)"),  # machine-independent effort
        "rsat_conflicts": _stat(out, r"c conflicts (\d+)"),
        "rsat_decisions": _stat(out, r"c decisions (\d+)"),
        "rsat_propagations": _stat(out, r"c propagations (\d+)"),
        "rsat_cpu_s": _stat(out, r"c cpu time ([\d.eE+-]+) s"),
    }


def opb_header(opb_text: str):
    """(pb_vars, pb_constraints) from the OPB '* #variable= V #constraint= C ...' header."""
    hdr = opb_text.splitlines()[0].split()
    return (int(hdr[hdr.index("#variable=") + 1]), int(hdr[hdr.index("#constraint=") + 1]))


def run_roundingsat(opb_path: Path, pbp_path: Path):
    """Solve OPB; return (row_dict, ok). ok ⇔ UNSAT proof produced."""
    t, status, out = timed([RSAT, str(opb_path), f"--proof-log={pbp_path}"])
    row = {"roundingsat_time_s": fmt(t), **parse_rsat(out)}
    if status == "TIMEOUT":
        row["roundingsat_status"] = "TIMEOUT"
        return row, False
    if "s UNSATISFIABLE" not in out:
        row["roundingsat_status"] = "NOT-UNSAT"
        return row, False
    row["roundingsat_status"] = "UNSAT"
    rl, rb = file_lines_bytes(pbp_path)
    row["rsat_log_lines"], row["rsat_log_bytes"] = rl, rb
    return row, True


def run_veripb(opb_path: Path, pbp_path: Path, kernel_path: Path):
    """veripb --elaborate; return (row_dict, ok). Leaves the kernel cert at kernel_path."""
    t, status, out = timed(["veripb", "--elaborate", str(kernel_path), str(opb_path), str(pbp_path)])
    row = {"veripb_elaborate_time_s": fmt(t)}
    if status == "TIMEOUT" or "s VERIFIED UNSATISFIABLE" not in out:
        row["veripb_proof_lines"] = status if status == "TIMEOUT" else "FAIL"
        return row, False
    kl, kb = file_lines_bytes(kernel_path)
    row["veripb_proof_lines"], row["veripb_proof_bytes"] = kl, kb
    row["kernel_cert_chars"] = len(kernel_path.read_text())
    return row, True
