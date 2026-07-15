#!/usr/bin/env python3
"""Single entry point for the LeanCSP experiments.

    python experiments/run.py preflight                 # check tools + build checkbench + veripb
    python experiments/run.py sbc     [--smoke] [fam...] # SBC speedup + checking-cost study
    python experiments/run.py scaling [--smoke]          # cutting-planes vs resolution proof size
    python experiments/run.py schur                      # Schur S(2)/S(3)/S(4) both pipelines, timed
    python experiments/run.py all     [--smoke]          # everything

Each subcommand runs a `preflight` first (tool check, builds the native `checkbench` exe and the
PBLean dependency). The SBC study additionally times the *in-Lean* checking cost via `lake build`,
which is only meaningful with a PRECOMPILED PBLean checker — preflight warns loudly if it is not.
See experiments/README.md for what each study measures and its external-tool requirements.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# tool -> (required?, description). roundingsat is found via $ROUNDINGSAT or PATH.
TOOLS = {
    "lake":       (True,  "Lean toolchain (via elan)"),
    "roundingsat":(True,  "pseudo-Boolean solver ($ROUNDINGSAT or PATH)"),
    "veripb":     (True,  "VeriPB pseudo-Boolean proof checker"),
    "minizinc":   (False, "MiniZinc + gecode/chuffed (schur SAT witnesses)"),
    "cadical":    (False, "SAT solver (scaling DRAT tier)"),
    "drat-trim":  (False, "DRAT proof checker (scaling DRAT tier)"),
}


def _have(tool: str) -> bool:
    if tool == "roundingsat":                      # $ROUNDINGSAT (a path) or on PATH
        p = os.environ.get("ROUNDINGSAT")
        return bool(p and Path(p).exists()) or shutil.which("roundingsat") is not None
    return shutil.which(tool) is not None


def _precompiled_veripb() -> bool:
    """True iff PBLean's kernel closure is built as a precompiled native lib (its .so is produced
    and gets loaded, so `ofReduceBool` runs the checker natively rather than interpreted)."""
    lib = REPO / ".lake" / "packages" / "veripb" / ".lake" / "build" / "lib"
    return bool(list(lib.glob("*VeriPBReflect*.so"))) if lib.exists() else False


def preflight(need_inlean: bool = True) -> None:
    print("== preflight ==", flush=True)
    for tool, (req, desc) in TOOLS.items():
        tag = "OK  " if _have(tool) else ("MISS" if req else "opt ")
        print(f"  {tag} {tool:12} {desc}", flush=True)
    missing = [t for t, (req, _) in TOOLS.items() if req and not _have(t)]
    if missing:
        sys.exit(f"\nERROR: required tools missing: {', '.join(missing)}")
    print("  building native checkbench exe + PBLean ...", flush=True)
    cb = subprocess.run(["lake", "build", "checkbench"], cwd=REPO, capture_output=True)
    subprocess.run(["lake", "build", "veripb"], cwd=REPO, capture_output=True)
    # Fail here, not an hour into the sweep: the SBC study shells out to this exe per instance, and
    # a missing binary surfaces as an uncaught FileNotFoundError inside native_check_time's Popen.
    if cb.returncode != 0 or not (REPO / ".lake" / "build" / "bin" / "checkbench").exists():
        sys.exit("\nERROR: `lake build checkbench` failed — the SBC study needs it to time the "
                 f"compiled checker.\n{cb.stderr.decode(errors='replace')[-1500:]}")
    if need_inlean and not _precompiled_veripb():
        print("\n  !! WARNING: PBLean is NOT precompiled (no VeriPBReflect .so found).\n"
              "     In-Lean checking times will be INTERPRETED (~10-20x slower) and NOT\n"
              "     representative of the precompiled pipeline. PBLean ships the precompiled\n"
              "     VeriPBReflect lib from v0.3.1 — check the `require veripb` pin in\n"
              "     lakefile.lean. See docs/PRECOMPILE_AND_TRUST.md.\n", flush=True)
    else:
        print("  OK   PBLean precompiled — in-Lean checking runs native" if need_inlean else "",
              flush=True)


def _run(script: str, argv: list[str]) -> None:
    subprocess.run([sys.executable, str(REPO / "experiments" / script), *argv], cwd=REPO, check=False)


def main() -> None:
    args = sys.argv[1:]
    if not args or args[0] in ("-h", "--help"):
        print(__doc__); return
    cmd, rest = args[0], args[1:]
    if cmd == "preflight":
        preflight(); return
    if cmd not in ("sbc", "scaling", "schur", "all"):
        print(__doc__); sys.exit(f"unknown command: {cmd}")
    preflight(need_inlean=(cmd in ("sbc", "all")))
    if cmd in ("sbc", "all"):
        _run("run_sbc.py", rest)
    if cmd in ("scaling", "all"):
        _run("run_scaling.py", rest)
    if cmd in ("schur", "all"):
        _run("run_schur_exact.py", [])   # schur has no --smoke / family args


if __name__ == "__main__":
    main()
