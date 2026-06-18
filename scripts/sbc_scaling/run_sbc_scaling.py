#!/usr/bin/env python3
"""v3 SBC scaling driver — symmetry-matched SBCs, two-tier (external sweep + Lean-verified subset).

Same CSV schema as v1 (results/sbc/), with the new v3 problem families and matched, *verified* SBCs.

Per family (one warm Lean process for all dumps, one `lake build` for native_decide):
  1. batch-dump every (instance, regime) OPB in ONE `lake env lean`,
  2. roundingsat (timeout 600 s) — record search effort + wall time for ALL regimes; a regime
     auto-stops once it times out (harder instances will too),
  3. veripb → certificate; record its size,
  4. **Lean tier**: if the certificate is small enough for native_decide (≤ LEAN_CAP), commit it
     and emit a `V3<Fam>Bench.lean` theorem; otherwise the instance is external-only,
  5. one `lake build V3<Fam>Bench` → native_decide-checks the Lean-tier theorems (per-family time).

Outputs to results/sbc_v3/ and CSP/L2S/Backends/PB/Bench/V3*Bench.lean (both gitignored — local only).
v1 outputs (results/sbc/, Bench/*Bench.lean) are untouched.

Usage: uv run python scripts/sbc_scaling/run_sbc_scaling.py [family ...]
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
BENCH = REPO / "CSP" / "L2S" / "Backends" / "PB" / "Bench"
CERTS = BENCH / "certs"
RESULTS = REPO / "results" / "sbc_v3"
LEAN_CAP = 500_000        # bytes; native_decide-verify a certificate only below this
SBC_DESC = F.SBC_DESC

# Same external columns as v1 (results/sbc/sbc_scaling.csv).  `size_param` is the family's
# natural scaling parameter, unique within each family.
EXT_COLUMNS = [
    "family", "size_param", "regime", "sbc",
    "pb_vars", "pb_constraints", "opb_bytes",
    "roundingsat_time_s", "roundingsat_status",
    "rsat_det_time", "rsat_conflicts", "rsat_decisions", "rsat_propagations", "rsat_cpu_s",
    "rsat_log_lines", "rsat_log_bytes",
    "veripb_proof_lines", "veripb_proof_bytes", "veripb_elaborate_time_s", "kernel_cert_chars",
]
LEAN_COLUMNS = ["family", "module", "n_theorems", "build_time_s", "build_time_per_theorem_s"]


def _cap(fam):
    return "".join(p[:1].upper() + p[1:] for p in fam.split("_"))


def emit_bench_module(fam, cfg, entries):
    """Emit the Lean-verified tier.  For value families a vp entry yields the END-TO-END
    `¬ base.isSatisfiableInt` via the family's verified `*_unsat_of_value_precedence` glue applied
    to the (small) extended cert.  A `none` entry verifies the base directly.  A `var` entry uses
    the family's verified variable-SBC glue (mutilated/matching/langford)."""
    cap = _cap(fam)
    imports = ["import CSP.L2S.Backends.PB.GenericEncode", f"import {cfg['module']}"]
    if cfg.get("glue_import") and cfg["glue_import"] != cfg["module"]:
        imports.append(f"import {cfg['glue_import']}")
    lines = imports + [
        "",
        f"namespace CSP.L2S.PB.Bench.V3{cap}",
        "open CSP.L2S CSP.L2S.PB IntCSP",
        "",
        f"/-! v3 SBC scaling bench (Lean-verified tier). {fam}: {cfg['note']}. -/",
        "",
    ]
    for e in entries:
        nm = f"{fam}_{e['label']}_{e['regime']}"
        cert_proof = f'csp_unsat_file ({e["ext"]}) {e["nv"]} "certs/{e["cert"]}"'
        if e["glue"]:                              # verified end-to-end: glue ∘ extended cert ⟹ base
            lines.append(f"theorem base_{nm} : ¬ ({e['base']}).isSatisfiableInt :=")
            lines.append(f"  {e['glue']} ({cert_proof})")
        elif e["regime"] == "none":                # none regime: cert verifies the base directly
            lines.append(f"theorem base_{nm} : ¬ ({e['base']}).isSatisfiableInt :=")
            lines.append(f'  csp_unsat_file ({e["base"]}) {e["nv"]} "certs/{e["cert"]}"')
        else:                                      # extended-unsat only (no verified glue for this SBC)
            lines.append(f"theorem ext_{nm} : ¬ ({e['ext']}).isSatisfiableInt :=")
            lines.append(f"  {cert_proof}")
        lines.append("")
    lines.append(f"end CSP.L2S.PB.Bench.V3{cap}")
    (BENCH / f"V3{cap}Bench.lean").write_text("\n".join(lines) + "\n")


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


def sweep_family(fam, ext_w, ext_fh):
    cfg = F.FAMILIES[fam]
    regimes = cfg["regimes"]
    module = f"CSP.L2S.Backends.PB.Bench.V3{_cap(fam)}Bench"
    print(f"\n===== {fam} ({cfg['note']}) =====", flush=True)
    items = [(f"{i['label']}_{rg}", F.regime_expr(cfg, i, rg))
             for i in cfg["instances"] for rg in regimes]
    print(f"  batch-dumping {len(items)} instances in one Lean process ...", flush=True)
    dumps = safe_dumps(cfg["module"], items)

    work = RESULTS / "_work"; work.mkdir(parents=True, exist_ok=True)
    CERTS.mkdir(parents=True, exist_ok=True)
    stopped = {rg: False for rg in regimes}
    entries = []
    for it in cfg["instances"]:                 # ascending hardness
        if all(stopped.values()):
            break
        for regime in regimes:
            if stopped[regime]:
                continue
            expr = F.regime_expr(cfg, it, regime)
            ext = {c: "" for c in EXT_COLUMNS}
            ext.update(family=fam, size_param=it["nat"], regime=regime, sbc=SBC_DESC[regime])
            if f"{it['label']}_{regime}" not in dumps:    # dump skipped (too big to encode)
                ext["roundingsat_status"] = "DUMP-FAIL"
                ext_w.writerow(ext); ext_fh.flush()
                print(f"  [{it['label']} {regime}] DUMP-FAIL (encode too slow) — skip", flush=True)
                continue
            nv, opb = dumps[f"{it['label']}_{regime}"]
            ext["pb_vars"], ext["pb_constraints"] = H.opb_header(opb)
            ext["opb_bytes"] = len(opb.encode())
            opbp = work / f"{fam}_{it['label']}_{regime}.opb"; opbp.write_text(opb)
            pbp = work / f"{fam}_{it['label']}_{regime}.pbp"
            cert = f"v3_{fam}_{it['label']}_{regime}.pbp"; kernel = CERTS / cert

            row, ok = H.run_roundingsat(opbp, pbp); ext.update(row)
            if not ok:
                ext_w.writerow(ext); ext_fh.flush()
                print(f"  [{it['label']} {regime}] roundingsat {ext['roundingsat_status']}", flush=True)
                if ext["roundingsat_status"] == "TIMEOUT":
                    stopped[regime] = True
                continue
            row, ok = H.run_veripb(opbp, pbp, kernel); ext.update(row); pbp.unlink(missing_ok=True)
            verified = ok and kernel.exists() and kernel.stat().st_size <= LEAN_CAP
            if ok and not verified:
                kernel.unlink(missing_ok=True)        # too big for native_decide → external-only
            if verified:
                glue = cfg["glue"](it) if (cfg.get("glue") and regime != "none") else None
                entries.append(dict(label=it["label"], base=it["expr"], ext=expr,
                                    nv=nv, cert=cert, regime=regime, glue=glue))
            ext_w.writerow(ext); ext_fh.flush()
            print(f"  [{it['label']} {regime}] vars={ext['pb_vars']} wall={ext['roundingsat_time_s']}s "
                  f"det={ext['rsat_det_time']} confl={ext['rsat_conflicts']} "
                  f"cert={ext.get('kernel_cert_chars','-')}ch lean={'Y' if verified else 'n'}", flush=True)

    emit_bench_module(fam, cfg, entries)
    n = len(entries)
    print(f"  verifying {module} ({n} theorems, native_decide) ...", flush=True)
    bt = lean_recheck.module_build_time(module) if n else 0.0
    per = bt / n if n else 0.0
    print(f"  native_decide build={bt:.1f}s over {n} theorems ({per:.2f}s/thm)", flush=True)
    return {"family": fam, "module": module, "n_theorems": n,
            "build_time_s": f"{bt:.1f}", "build_time_per_theorem_s": f"{per:.3f}"}


def main():
    fams = sys.argv[1:] or list(F.FAMILIES.keys())
    RESULTS.mkdir(parents=True, exist_ok=True)
    ext_path = RESULTS / "sbc_scaling.csv"; lean_path = RESULTS / "sbc_scaling_lean.csv"
    new_ext = not ext_path.exists(); new_lean = not lean_path.exists()
    with open(ext_path, "a", newline="") as ext_fh, open(lean_path, "a", newline="") as lean_fh:
        ext_w = csv.DictWriter(ext_fh, fieldnames=EXT_COLUMNS)
        lean_w = csv.DictWriter(lean_fh, fieldnames=LEAN_COLUMNS)
        if new_ext:
            ext_w.writeheader()
        if new_lean:
            lean_w.writeheader()
        for fam in fams:
            lean_w.writerow(sweep_family(fam, ext_w, ext_fh)); lean_fh.flush()


if __name__ == "__main__":
    main()
