#!/usr/bin/env python3
"""SBC scaling sweep — symmetry-matched SBCs, per instance measuring solver effort *and*
our own pipeline's in-Lean checking cost.

Per family (one warm Lean process for all OPB dumps):
  1. batch-dump every (instance, regime) OPB in ONE `lake env lean`,
  2. roundingsat (timeout 600 s) — record wall time (median-of-3), deterministic time, and
     search-effort counters for ALL regimes; a regime auto-stops once it times out,
  3. veripb --elaborate → kernel certificate (kept locally under artifacts/); record its size,
  4. **pipeline cost**: for every cert that fits the in-Lean check cap, run PBLean's verified
     checker on it inside Lean and record `check_us` (the compiled `checkProofBool` runtime —
     exactly what `Lean.ofReduceBool` reduces, per docs/MIGRATION_ofReduceBool.md) and
     `verify_wall_s` (the whole reflected-term elaborate+compile+check, minus import baseline).

Unlike the old v3 driver this does **not** emit `V3*Bench.lean` modules or `lake build` them:
the per-instance `check_us` is the real pipeline cost and needs no source-tree writes. All
generated files (opb, pbp certs) stay under experiments/sbc/artifacts/ (gitignored); the
per-instance CSV under experiments/sbc/results/ is committed. `aggregate.py` turns it into the
geometric-mean paper table (`sbc_table.csv`); `plot.py` draws the supplementary figures.

Usage: uv run python experiments/lib/sbc_sweep.py [family ...]   (or via experiments/run_sbc.py)
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

import families as F
import harness as H
import lean_dump
import lean_recheck

REPO = Path(__file__).resolve().parent.parent.parent
RESULTS = REPO / "experiments" / "sbc" / "results"        # committed per-instance CSV
WORK = REPO / "experiments" / "sbc" / "artifacts"         # opb scratch (git-excluded)
CERTS = WORK / "certs"                                    # kernel certs (git-excluded)
LEAN_CAP = 500_000        # bytes; run the in-Lean check only for certs below this
SBC_DESC = F.SBC_DESC

# `size_param` is the family's natural scaling parameter, unique within each family.
# `roundingsat_time_s` is median-of-3 wall; `rsat_det_time` is the machine-independent
# deterministic effort (kept as a robustness cross-check).  `check_us` / `verify_wall_s` are
# our pipeline's own PBLean checking cost (see module docstring).
EXT_COLUMNS = [
    "family", "size_param", "regime", "sbc",
    "pb_vars", "pb_constraints", "opb_bytes",
    "roundingsat_time_s", "roundingsat_status",
    "rsat_det_time", "rsat_conflicts", "rsat_decisions", "rsat_propagations", "rsat_cpu_s",
    "rsat_log_lines", "rsat_log_bytes",
    "veripb_proof_lines", "veripb_proof_bytes", "veripb_elaborate_time_s", "kernel_cert_chars",
    "check_us", "verify_wall_s",
]


def safe_dumps(module, items, batch_to=900, per_to=240):
    """Batch-dump in one process; on failure fall back to per-instance dumps so one slow
    `encodeCSP` (e.g. a huge instance) skips itself instead of killing the whole family."""
    try:
        return lean_dump.dump_batch(module, items, timeout=batch_to)
    except Exception:
        print("  batch dump failed — per-instance fallback (slow instances will be skipped)", flush=True)
        out = {}
        for tag, expr in items:
            try:
                out[tag] = lean_dump.dump(module, expr, timeout=per_to)
            except Exception:
                print(f"    DUMP-SKIP {tag}", flush=True)
        return out


def sweep_family(fam, ext_w, ext_fh, limit=None):
    cfg = F.FAMILIES[fam]
    regimes = cfg["regimes"]
    module = cfg["module"]          # the Lean module that defines this family's CSP terms
    # instances are listed in ascending hardness; `limit` keeps only the smallest few (smoke test)
    insts = cfg["instances"] if limit is None else cfg["instances"][:limit]
    print(f"\n===== {fam} ({cfg['note']}) =====", flush=True)
    items = [(f"{i['label']}_{rg}", F.regime_expr(cfg, i, rg))
             for i in insts for rg in regimes]
    print(f"  batch-dumping {len(items)} instances in one Lean process ...", flush=True)
    dumps = safe_dumps(module, items)

    WORK.mkdir(parents=True, exist_ok=True)
    CERTS.mkdir(parents=True, exist_ok=True)
    stopped = {rg: False for rg in regimes}
    base = None                     # per-family import-only baseline for verify_wall_s (lazy)
    for it in insts:                            # ascending hardness
        if all(stopped.values()):
            break
        for regime in regimes:
            if stopped[regime]:
                continue
            expr = F.regime_expr(cfg, it, regime)
            tag = f"{it['label']}_{regime}"
            ext = {c: "" for c in EXT_COLUMNS}
            ext.update(family=fam, size_param=it["nat"], regime=regime, sbc=SBC_DESC[regime])
            if tag not in dumps:                # dump skipped (too big to encode)
                ext["roundingsat_status"] = "DUMP-FAIL"
                ext_w.writerow(ext); ext_fh.flush()
                print(f"  [{tag}] DUMP-FAIL (encode too slow) — skip", flush=True)
                continue
            nv, opb = dumps[tag]
            ext["pb_vars"], ext["pb_constraints"] = H.opb_header(opb)
            ext["opb_bytes"] = len(opb.encode())
            opbp = WORK / f"{fam}_{tag}.opb"; opbp.write_text(opb)
            pbp = WORK / f"{fam}_{tag}.pbp"
            cert = f"sbc_{fam}_{tag}.pbp"; kernel = CERTS / cert

            row, ok = H.run_roundingsat(opbp, pbp); ext.update(row)
            if not ok:
                ext_w.writerow(ext); ext_fh.flush()
                print(f"  [{tag}] roundingsat {ext['roundingsat_status']}", flush=True)
                if ext["roundingsat_status"] == "TIMEOUT":
                    stopped[regime] = True
                continue
            row, ok = H.run_veripb(opbp, pbp, kernel); ext.update(row); pbp.unlink(missing_ok=True)
            fits = ok and kernel.exists() and kernel.stat().st_size <= LEAN_CAP
            if ok and not fits:                 # cert too big for the in-Lean check pass
                ext["verify_wall_s"] = "OVER-CAP"
            if fits:
                if base is None:                # ~5 import-only walls, paid once per family
                    base = lean_recheck.baseline(module)
                wall, _enc_us, chk_us, cok = lean_recheck.runtime_split(
                    module, expr, nv, str(kernel.resolve()), base)
                if cok:
                    ext["check_us"] = chk_us
                    ext["verify_wall_s"] = "" if wall is None else f"{wall:.2f}"
                else:
                    ext["verify_wall_s"] = "CHECK-FAIL"
            ext_w.writerow(ext); ext_fh.flush()
            print(f"  [{tag}] vars={ext['pb_vars']} wall={ext['roundingsat_time_s']}s "
                  f"det={ext['rsat_det_time']} cert={ext.get('kernel_cert_chars','-')}ch "
                  f"check={ext.get('check_us','-')}us verify={ext.get('verify_wall_s','-')}s",
                  flush=True)


def main():
    argv = sys.argv[1:]
    smoke = "--smoke" in argv                        # only the 2 smallest instances per family
    argv_fams = [a for a in argv if not a.startswith("-")]
    fams = argv_fams or list(F.FAMILIES.keys())
    limit = 2 if smoke else None
    RESULTS.mkdir(parents=True, exist_ok=True)
    WORK.mkdir(parents=True, exist_ok=True)
    # Smoke output goes to a separate, gitignored file so it never pollutes committed results.
    ext_path = RESULTS / ("sbc_scaling.smoke.csv" if smoke else "sbc_scaling.csv")
    # Smoke and full-sweep (no family args) start clean; a named subset appends.
    mode = "a" if (argv_fams and not smoke and ext_path.exists()) else "w"
    with open(ext_path, mode, newline="") as ext_fh:
        ext_w = csv.DictWriter(ext_fh, fieldnames=EXT_COLUMNS)
        if mode == "w":
            ext_w.writeheader()
        for fam in fams:
            sweep_family(fam, ext_w, ext_fh, limit)
    print(f"\nwrote {ext_path}")


if __name__ == "__main__":
    main()
