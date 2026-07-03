#!/usr/bin/env python3
"""Lean-verified tier for the PB scaling study — check the certificates *inside Lean*.

The external sweep (run_scaling.py) produces a kernel certificate per instance and records its
size, then deletes it.  This driver instead keeps the certificate and kernel-checks it in Lean:
for each (family, size) whose certificate fits the native_decide cap, it

  1. dumps the canonical OPB of the *parametric base CSP* straight from Lean (lean_dump) — so the
     certificate is valid for the `csp_unsat_file` theorem by construction, independent of pbgen,
  2. roundingsat -> .pbp  ->  veripb --elaborate -> kernel certificate (kept under Bench/certs/),
  3. emits a one-line `csp_unsat_file <csp> <nv> "certs/..."` theorem (= `¬ csp.isSatisfiableInt`,
     PBLean's verified checker run via native_decide on the committed cert),
  4. `lake build`s the generated module so native_decide kernel-checks every instance at once,
  5. times each instance's native_decide recheck individually (recheck-minus-baseline).

This extends results/scaling_lean.csv from the 9 hand-committed checkpoints to the whole generated
ladder.  Because these families are cutting-planes-easy their certs stay small, so native_decide
verifies far up the ladder (the cap only excludes the rare oversized cert).

Outputs: results/scaling_lean.csv and CSP/L2S/Backends/PB/Bench/Scaling*Bench.lean (+ certs/);
the Bench artifacts are gitignored (local-only), like the SBC v3 tier.

Usage:  uv run python scripts/scaling/run_lean_tier.py [family ...]
"""
from __future__ import annotations

import csv
import sys
from pathlib import Path

# reuse the battle-tested SBC harness modules (dump / recheck / roundingsat+veripb)
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "sbc_scaling"))
import harness as H          # noqa: E402
import lean_dump             # noqa: E402
import lean_recheck          # noqa: E402

REPO = Path(__file__).resolve().parent.parent.parent
BENCH = REPO / "CSP" / "L2S" / "Backends" / "PB" / "Bench"
CERTS = BENCH / "certs"
WORK = REPO / "results" / "_work_lean"
OUT = REPO / "results" / "scaling_lean.csv"
LEAN_CAP = 500_000           # bytes; native_decide-verify a certificate only below this

COLUMNS = ["family", "size_param", "pb_vars", "pb_constraints",
           "kernel_cert_chars", "verified",
           "encode_us",                 # encoder RUNTIME (build the formula), microseconds
           "check_us",                  # PBLean checkProofBool RUNTIME on the cert, microseconds
           "verify_wall_s",             # one-process wall − baseline ≈ compiling the reflected term
           "module_build_time_s"]       # per-family `lake build` (native_decide kernel-checks all)


def _cycle_lit(n):
    return "[" + ", ".join(f"({i}, {(i + 1) % n})" for i in range(n)) + "]"


# Parametric BASE CSP per family (the same terms the external sweep encodes, no SBC).  `sizes` is
# the native_decide ladder: the PB sweep's range, trimmed for families where native_decide on a
# huge instance would dominate (oddcycle is the easy control — a representative prefix suffices).
FAMILIES = {
    "php": dict(
        module="CSP.L2S.Proofs.PigeonholeValuePrecedence",
        expr=lambda h: f"Pigeonhole.php_sb {h + 1} {h}",
        sizes=list(range(2, 21))),
    "mutilated": dict(
        module="CSP.L2S.Backends.PB.Bench.Generators",
        expr=lambda k: f"Bench.gen_mutilated {k}",
        sizes=[2, 3, 4, 5, 6, 7, 8]),
    "oddcycle": dict(
        module="CSP.L2S.Proofs.GraphColoringSB",
        expr=lambda n: f"graph_coloring_csp {n} {_cycle_lit(n)} 2",
        sizes=[3, 5, 7, 9, 11, 15, 21, 31, 51, 75, 101]),
}


def _cap(fam):
    return "".join(p[:1].upper() + p[1:] for p in fam.split("_"))


def emit_module(fam, module_lean, entries):
    """Write Bench/Scaling<Fam>Bench.lean — one `csp_unsat_file` theorem per verified instance."""
    cap = _cap(fam)
    lines = [
        "import CSP.L2S.Backends.PB.GenericEncode",
        f"import {FAMILIES[fam]['module']}",
        "",
        f"namespace CSP.L2S.PB.Bench.Scaling{cap}",
        "open CSP.L2S CSP.L2S.PB IntCSP",
        "",
        f"/-! PB scaling study — Lean-verified tier for `{fam}` "
        "(native_decide kernel-checks each cert). -/",
        "",
    ]
    for e in entries:
        nm = f"{fam}_{e['size']}"
        lines.append(f"theorem base_{nm} : ¬ ({e['expr']}).isSatisfiableInt :=")
        lines.append(f'  csp_unsat_file ({e["expr"]}) {e["nv"]} "certs/{e["cert"]}"')
        lines.append("")
    lines.append(f"end CSP.L2S.PB.Bench.Scaling{cap}")
    (BENCH / f"Scaling{cap}Bench.lean").write_text("\n".join(lines) + "\n")


def sweep_family(fam, writer, fh):
    cfg = FAMILIES[fam]
    cap = _cap(fam)
    module_lean = f"CSP.L2S.Backends.PB.Bench.Scaling{cap}Bench"
    print(f"\n===== {fam} =====", flush=True)
    items = [(str(s), cfg["expr"](s)) for s in cfg["sizes"]]
    print(f"  batch-dumping {len(items)} instances in one Lean process ...", flush=True)
    dumps = lean_dump.dump_batch(cfg["module"], items)

    WORK.mkdir(parents=True, exist_ok=True)
    CERTS.mkdir(parents=True, exist_ok=True)
    rows, entries = {}, []
    for s in cfg["sizes"]:
        row = {c: "" for c in COLUMNS}
        row["family"], row["size_param"] = fam, s
        rows[s] = row
        if str(s) not in dumps:
            row["verified"] = "DUMP-FAIL"
            print(f"  [{fam} {s}] DUMP-FAIL — skip", flush=True)
            continue
        nv, opb = dumps[str(s)]
        expr = cfg["expr"](s)
        row["pb_vars"], row["pb_constraints"] = H.opb_header(opb)
        opbp = WORK / f"{fam}_{s}.opb"; opbp.write_text(opb)
        pbp = WORK / f"{fam}_{s}.pbp"
        cert = f"scaling_{fam}_{s}.pbp"; kernel = CERTS / cert

        r, ok = H.run_roundingsat(opbp, pbp)
        if not ok:
            row["verified"] = r["roundingsat_status"]
            print(f"  [{fam} {s}] roundingsat {r['roundingsat_status']}", flush=True)
            continue
        r, ok = H.run_veripb(opbp, pbp, kernel); pbp.unlink(missing_ok=True)
        row["kernel_cert_chars"] = r.get("kernel_cert_chars", "")
        if not (ok and kernel.exists() and kernel.stat().st_size <= LEAN_CAP):
            kernel.unlink(missing_ok=True)
            row["verified"] = "OVER-CAP" if ok else "VERIPB-FAIL"
            print(f"  [{fam} {s}] cert too big / veripb fail — external-only", flush=True)
            continue
        entries.append(dict(size=s, expr=expr, nv=nv, cert=cert))
        print(f"  [{fam} {s}] vars={row['pb_vars']} cert={row['kernel_cert_chars']}ch -> Lean tier",
              flush=True)

    # Emit + build the module: native_decide kernel-checks every theorem in one warm process.
    emit_module(fam, module_lean, entries)
    n = len(entries)
    print(f"  building {module_lean} ({n} theorems, native_decide) ...", flush=True)
    bt = lean_recheck.module_build_time(module_lean) if n else 0.0
    print(f"  module build={bt:.1f}s over {n} theorems", flush=True)

    # Per-instance runtime split: in ONE process, time the compiled encoder and the compiled
    # checker (checkProofBool — exactly what native_decide's ofReduceBool reduces) separately, via
    # Lean's monotonic clock.  No cross-run subtraction: both phases share one clock, startup is
    # paid once outside both.  The process wall (− baseline) ≈ the cost of *compiling* the reflected
    # term, which is what scales to seconds — the runtimes themselves stay sub-millisecond.
    base = lean_recheck.baseline(cfg["module"]) if n else 0.0
    for e in entries:
        row = rows[e["size"]]
        wall, enc_us, chk_us, ok = lean_recheck.runtime_split(
            cfg["module"], e["expr"], e["nv"], str((CERTS / e["cert"]).resolve()), base)
        row["verified"] = "Y" if ok else "ND-FAIL"
        row["encode_us"] = "" if enc_us is None else str(enc_us)
        row["check_us"] = "" if chk_us is None else str(chk_us)
        row["verify_wall_s"] = "" if wall is None else f"{wall:.1f}"
        print(f"    {fam} {e['size']}: encode={row['encode_us']}us check={row['check_us']}us "
              f"wall={row['verify_wall_s']}s ({'ok' if ok else 'FAIL'})", flush=True)
    if entries:                                  # attach module build to the largest verified row
        rows[entries[-1]["size"]]["module_build_time_s"] = f"{bt:.1f}"

    for s in cfg["sizes"]:
        writer.writerow(rows[s]); fh.flush()


def main():
    fams = sys.argv[1:] or list(FAMILIES.keys())
    OUT.parent.mkdir(parents=True, exist_ok=True)
    WORK.mkdir(parents=True, exist_ok=True)
    with open(OUT, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS)
        w.writeheader()
        for fam in fams:
            sweep_family(fam, w, fh)
    import shutil
    shutil.rmtree(WORK, ignore_errors=True)
    print(f"\nWrote {OUT}")


if __name__ == "__main__":
    main()
