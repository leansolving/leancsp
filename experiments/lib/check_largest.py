#!/usr/bin/env python3
from __future__ import annotations

import csv
import sys
from pathlib import Path

import families as F
import harness as H
import lean_dump
import lean_recheck

REPO = Path(__file__).resolve().parent.parent.parent
RES = REPO / "experiments" / "sbc" / "results"
WORK = REPO / "experiments" / "sbc" / "artifacts" / "largest"
COLUMNS = ["family", "regime", "size_param", "num_vars", "cert_bytes",
           "check_ns", "check_pretty", "num_constraints", "status"]
# The compiled checker runs at ~0.1 MB/s, so a cert much past this can't finish under CHECK_TIMEOUT;
# we record it as impractical by size rather than waste time regenerating 100s of MB and timing out.
MAX_CHECK_BYTES = 40_000_000
CHECK_TIMEOUT = 600


def targets(fams):
    """Per (family, regime): the solved instance with the largest certificate."""
    best = {}
    for r in csv.DictReader(open(RES / "sbc_scaling.csv")):
        if (r["family"] in fams and r["roundingsat_status"] == "UNSAT"
                and r["kernel_cert_chars"]):
            c = int(r["kernel_cert_chars"])
            k = (r["family"], r["regime"])
            if k not in best or c > best[k][0]:
                best[k] = (c, int(r["size_param"]))
    return best


def pretty(ns):
    if ns is None:
        return "-"
    us = ns / 1e3
    if us < 1000:
        return f"{us:.0f}us"
    if us < 1e6:
        return f"{us / 1e3:.1f}ms"
    return f"{us / 1e6:.2f}s"


def find_inst(cfg, size):
    return next((it for it in cfg["instances"] if it["nat"] == size), None)


def measure(fam, regime, size, known_cert, w, fh):
    cfg = F.FAMILIES[fam]
    it = find_inst(cfg, size)
    row = {c: "" for c in COLUMNS}
    row.update(family=fam, regime=regime, size_param=size)
    if it is None:
        row["status"] = "NO-INSTANCE"; w.writerow(row); fh.flush(); return
    if known_cert > MAX_CHECK_BYTES:            # too big to check under the timeout — skip by size
        row["cert_bytes"] = known_cert
        row["status"] = "TOO-LARGE"
        w.writerow(row); fh.flush()
        print(f"  [{fam} {regime} n={size}] cert={known_cert}B (~{known_cert/1e6:.0f} MB) "
              "TOO-LARGE — checking impractical", flush=True)
        return
    expr = F.regime_expr(cfg, it, regime)
    try:
        nv, opb = lean_dump.dump(cfg["module"], expr, timeout=1800)
    except Exception:
        row["status"] = "DUMP-FAIL"; w.writerow(row); fh.flush(); return
    row["num_vars"] = nv
    WORK.mkdir(parents=True, exist_ok=True)
    opbp = WORK / f"{fam}_{regime}.opb"; opbp.write_text(opb)
    pbp = WORK / f"{fam}_{regime}.pbp"
    kernel = WORK / f"{fam}_{regime}_kernel.pbp"
    r, ok = H.run_roundingsat(opbp, pbp)
    if not ok:
        row["status"] = "RSAT-" + r.get("roundingsat_status", "FAIL")
        w.writerow(row); fh.flush(); return
    r, ok = H.run_veripb(opbp, pbp, kernel); pbp.unlink(missing_ok=True)
    if not (ok and kernel.exists()):
        row["status"] = "VERIPB-FAIL"; w.writerow(row); fh.flush(); return
    row["cert_bytes"] = kernel.stat().st_size
    ns, cok, ncons, _plen = lean_recheck.check_file_runtime(
        cfg["module"], expr, nv, str(kernel.resolve()), timeout=CHECK_TIMEOUT)
    kernel.unlink(missing_ok=True); opbp.unlink(missing_ok=True)   # free the (huge) cert
    row["check_ns"] = "" if ns is None else ns
    row["check_pretty"] = pretty(ns)
    row["num_constraints"] = "" if ncons is None else ncons
    row["status"] = "OK" if cok else (f"CHECK->{CHECK_TIMEOUT}s" if ns is None else "CHECK-FALSE")
    w.writerow(row); fh.flush()
    print(f"  [{fam} {regime} n={size}] cert={row['cert_bytes']}B "
          f"check={row['check_pretty']} {row['status']}", flush=True)


def main():
    fams = sys.argv[1:] or list(F.FAMILIES.keys())
    RES.mkdir(parents=True, exist_ok=True)
    tg = targets(set(fams))
    out = RES / "check_largest.csv"
    with open(out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=COLUMNS)
        w.writeheader()
        for (fam, regime), (c, size) in sorted(tg.items()):
            print(f"=== {fam} {regime}: largest cert n={size} (~{c / 1e6:.1f} MB) ===", flush=True)
            measure(fam, regime, size, c, w, fh)
    print(f"\nwrote {out}")


if __name__ == "__main__":
    main()
