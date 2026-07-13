#!/usr/bin/env python3
from __future__ import annotations

import csv
import sys
from pathlib import Path

# shared harness modules now live alongside this file in experiments/lib/
import harness as H          # noqa: E402
import lean_dump             # noqa: E402
import lean_recheck          # noqa: E402

REPO = Path(__file__).resolve().parent.parent.parent
# The Lean-verified tier still emits gitignored bench modules under the source tree, because
# `lake build` only kernel-checks modules that live under CSP/ (see experiments/README.md).
BENCH = REPO / "CSP" / "L2S" / "Backends" / "PB" / "Bench"
CERTS = BENCH / "certs"
WORK = REPO / "experiments" / "scaling" / "artifacts" / "_work_lean"
OUT = REPO / "experiments" / "scaling" / "results" / "scaling_lean.csv"
LEAN_CAP = 500_000           # bytes; in-Lean check a certificate only below this

COLUMNS = ["family", "size_param", "pb_vars", "pb_constraints",
           "kernel_cert_chars", "verified",
           "encode_us",                 # encoder RUNTIME (build the formula), microseconds
           "check_us",                  # PBLean checkProofBool RUNTIME on the cert, microseconds
           "verify_wall_s",             # one-process wall − baseline ≈ compiling the reflected term
           "module_build_time_s"]       # per-family `lake build` (ofReduceBool kernel-checks all)


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
        "(an ofReduceBool reflection kernel-checks each cert). -/",
        "",
    ]
    for e in entries:
        nm = f"{fam}_{e['size']}"
        lines.append(f"theorem base_{nm} : ¬ ({e['expr']}).isSatisfiableInt :=")
        lines.append(f'  csp_unsat_file ({e["expr"]}) {e["nv"]} "certs/{e["cert"]}"')
        lines.append("")
    lines.append(f"end CSP.L2S.PB.Bench.Scaling{cap}")
    (BENCH / f"Scaling{cap}Bench.lean").write_text("\n".join(lines) + "\n")


def sweep_family(fam, writer, fh, limit=None):
    cfg = FAMILIES[fam]
    cap = _cap(fam)
    module_lean = f"CSP.L2S.Backends.PB.Bench.Scaling{cap}Bench"
    sizes = cfg["sizes"] if limit is None else cfg["sizes"][:limit]  # smallest few (smoke test)
    print(f"\n===== {fam} =====", flush=True)
    items = [(str(s), cfg["expr"](s)) for s in sizes]
    print(f"  batch-dumping {len(items)} instances in one Lean process ...", flush=True)
    dumps = lean_dump.dump_batch(cfg["module"], items)

    WORK.mkdir(parents=True, exist_ok=True)
    CERTS.mkdir(parents=True, exist_ok=True)
    rows, entries = {}, []
    for s in sizes:
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

    # Emit + build the module: ofReduceBool reflection kernel-checks every theorem in one process.
    emit_module(fam, module_lean, entries)
    n = len(entries)
    print(f"  building {module_lean} ({n} theorems, ofReduceBool) ...", flush=True)
    bt = lean_recheck.module_build_time(module_lean) if n else 0.0
    print(f"  module build={bt:.1f}s over {n} theorems", flush=True)

    # Per-instance runtime split: in ONE process, time the compiled encoder and the compiled
    # checker (checkProofBool — exactly what the committed ofReduceBool reflection reduces) via
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

    for s in sizes:
        writer.writerow(rows[s]); fh.flush()


def main():
    argv = sys.argv[1:]
    smoke = "--smoke" in argv                          # only the 2 smallest sizes per family
    fams = [a for a in argv if not a.startswith("-")] or list(FAMILIES.keys())
    limit = 2 if smoke else None
    out_path = OUT.with_name(f"scaling_lean{'.smoke' if smoke else ''}.csv")
    out_path.parent.mkdir(parents=True, exist_ok=True)
    WORK.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS)
        w.writeheader()
        for fam in fams:
            sweep_family(fam, w, fh, limit)
    import shutil
    shutil.rmtree(WORK, ignore_errors=True)
    print(f"\nWrote {out_path}")


if __name__ == "__main__":
    main()
