#!/usr/bin/env python3
from __future__ import annotations

import csv
import sys
from pathlib import Path

import families as F
import harness as H
import lean_dump
import lean_recheck as LR

REPO = Path(__file__).resolve().parent.parent.parent
RESULTS = REPO / "experiments" / "sbc" / "results"        # committed per-instance CSV
WORK = REPO / "experiments" / "sbc" / "artifacts"         # opb / cert scratch (git-excluded)
CERTS = WORK / "certs"                                    # kernel certs (git-excluded)
SBC_DESC = F.SBC_DESC

# Everything is measured PER INSTANCE, for BOTH regimes (w/o SBC = "none", w/ SBC):
# `roundingsat_time_s` is median-of-3 wall; `rsat_det_time` the machine-independent deterministic
# effort. `check_ns` is the native compiled `checkProofBool` runtime (cert pre-loaded). `pipeline_*`
# is the full in-Lean `lake build` cost of one `csp_unsat_file` reflection theorem with a PRECOMPILED
# checker (net of the fixed per-build overhead) — the honest cost the committed artifact pays.
EXT_COLUMNS = [
    "family", "size_param", "regime", "sbc",
    "pb_vars", "pb_constraints", "opb_bytes",
    "roundingsat_time_s", "roundingsat_status",
    "rsat_det_time", "rsat_conflicts", "rsat_decisions", "rsat_propagations", "rsat_cpu_s",
    "rsat_log_lines", "rsat_log_bytes",
    "veripb_proof_lines", "veripb_proof_bytes", "veripb_elaborate_time_s", "kernel_cert_chars",
    "check_ns", "check_status", "pipeline_gross_s", "pipeline_net_s", "pipeline_status",
]


def _cleanup(*paths):
    for p in paths:
        Path(p).unlink(missing_ok=True)


def sweep_family(fam, ext_w, ext_fh, baseline_cache, limit=None):
    cfg = F.FAMILIES[fam]
    regimes = cfg["regimes"]
    module = cfg["module"]          # the Lean module that defines this family's CSP terms
    # instances are listed in ascending hardness; `limit` keeps only the smallest few (smoke test)
    insts = cfg["instances"] if limit is None else cfg["instances"][:limit]
    print(f"\n===== {fam} ({cfg['note']}) =====", flush=True)
    WORK.mkdir(parents=True, exist_ok=True)
    CERTS.mkdir(parents=True, exist_ok=True)
    stopped = {rg: False for rg in regimes}
    for it in insts:                            # ascending hardness
        if all(stopped.values()):
            break
        for regime in regimes:                  # both w/o SBC ("none") and w/ SBC
            if stopped[regime]:
                continue
            expr = F.regime_expr(cfg, it, regime)
            tag = f"{it['label']}_{regime}"
            ext = {c: "" for c in EXT_COLUMNS}
            ext.update(family=fam, size_param=it["nat"], regime=regime, sbc=SBC_DESC[regime])
            opbp = WORK / f"{fam}_{tag}.opb"; pbp = WORK / f"{fam}_{tag}.pbp"
            constrs = WORK / f"{fam}_{tag}.cs"; kernel = CERTS / f"sbc_{fam}_{tag}.pbp"
            try:                                # OPB + serialized constraints (for checkbench) in one dump
                nv, opb = lean_dump.dump_with_constrs(module, expr, str(constrs.resolve()))
            except Exception as e:              # timeout, elaboration error, OOM — report which
                ext["roundingsat_status"] = "DUMP-FAIL"; ext_w.writerow(ext); ext_fh.flush()
                print(f"  [{tag}] DUMP-FAIL — skip: {type(e).__name__}: {e}", flush=True); continue
            ext["pb_vars"], ext["pb_constraints"] = H.opb_header(opb)
            ext["opb_bytes"] = len(opb.encode()); opbp.write_text(opb)

            row, ok = H.run_roundingsat(opbp, pbp); ext.update(row)      # solve
            if not ok:
                if ext["roundingsat_status"] == "TIMEOUT":
                    stopped[regime] = True
                _cleanup(opbp, pbp, constrs)
                ext_w.writerow(ext); ext_fh.flush()
                print(f"  [{tag}] roundingsat {ext['roundingsat_status']}", flush=True); continue
            row, ok = H.run_veripb(opbp, pbp, kernel); ext.update(row); pbp.unlink(missing_ok=True)  # cert
            if ok and kernel.exists():
                ns, cok = LR.native_check_time(str(constrs.resolve()), nv, str(kernel.resolve()))  # native
                ext["check_ns"] = "" if ns is None else ns
                ext["check_status"] = "OK" if cok else ("TIMEOUT" if ns is None else "FALSE")
                net, gross, pstat = LR.pipeline_build_time(                                         # in-Lean
                    module, expr, nv, str(kernel.resolve()), baseline_cache)
                ext["pipeline_gross_s"] = "" if gross is None else gross
                ext["pipeline_net_s"] = "" if net is None else net
                ext["pipeline_status"] = pstat
            else:                               # veripb produced no cert: nothing to check or reflect
                ext["check_status"] = ext["pipeline_status"] = "NO-CERT"
            _cleanup(opbp, constrs, kernel)
            ext_w.writerow(ext); ext_fh.flush()
            print(f"  [{tag}] vars={ext['pb_vars']} rsat={ext['roundingsat_time_s']}s "
                  f"cert={ext.get('kernel_cert_chars','-')}ch check={ext.get('check_ns','-')}ns "
                  f"pipe={ext.get('pipeline_net_s','-')}s({ext.get('pipeline_status','-')})", flush=True)


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
    baseline_cache = {}                              # per-import empty-module build baseline (in-Lean tier)
    with open(ext_path, mode, newline="") as ext_fh:
        ext_w = csv.DictWriter(ext_fh, fieldnames=EXT_COLUMNS)
        if mode == "w":
            ext_w.writeheader()
        for fam in fams:
            sweep_family(fam, ext_w, ext_fh, baseline_cache, limit)
    print(f"\nwrote {ext_path}")


if __name__ == "__main__":
    main()
