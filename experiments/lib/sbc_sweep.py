#!/usr/bin/env python3
from __future__ import annotations

import csv
import sys
from pathlib import Path

import families as F
import harness as H
import lean_dump

REPO = Path(__file__).resolve().parent.parent.parent
RESULTS = REPO / "experiments" / "sbc" / "results"        # committed per-instance CSV
WORK = REPO / "experiments" / "sbc" / "artifacts"         # opb / cert scratch (git-excluded)
CERTS = WORK / "certs"                                    # kernel certs (git-excluded)
SBC_DESC = F.SBC_DESC

# `size_param` is the family's natural scaling parameter, unique within each family.
# `roundingsat_time_s` is median-of-3 wall; `rsat_det_time` is the machine-independent
# deterministic effort.  The in-Lean checking cost is measured separately, on the largest
# certificate per family, by check_largest.py — not per instance here.
EXT_COLUMNS = [
    "family", "size_param", "regime", "sbc",
    "pb_vars", "pb_constraints", "opb_bytes",
    "roundingsat_time_s", "roundingsat_status",
    "rsat_det_time", "rsat_conflicts", "rsat_decisions", "rsat_propagations", "rsat_cpu_s",
    "rsat_log_lines", "rsat_log_bytes",
    "veripb_proof_lines", "veripb_proof_bytes", "veripb_elaborate_time_s", "kernel_cert_chars",
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
            row, ok = H.run_veripb(opbp, pbp, kernel); ext.update(row)
            pbp.unlink(missing_ok=True); kernel.unlink(missing_ok=True)   # keep only the size
            ext_w.writerow(ext); ext_fh.flush()
            print(f"  [{tag}] vars={ext['pb_vars']} wall={ext['roundingsat_time_s']}s "
                  f"det={ext['rsat_det_time']} cert={ext.get('kernel_cert_chars','-')}ch", flush=True)


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
