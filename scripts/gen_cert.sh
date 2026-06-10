#!/usr/bin/env bash
# Regenerate a VeriPB kernel certificate for one CSP against the *canonical*
# generic encoder (`encodeCSP`), and commit it under Problems/certs/<out>.pbp.
#
# Usage: scripts/gen_cert.sh <Module> <cspExpr> <out>
#   <Module>      the module defining the CSP, e.g. CSP.L2S.Tests.lean.«02_color»
#                 or CSP.L2S.Backends.PB.Problems.Sudoku
#   <cspExpr>     a Lean term of type IntCSP, e.g. k3_2col
#   <out>         certificate base name, e.g. k3   (-> Problems/certs/k3.pbp)
#
# Prints `numVars=<N>` — the OPB #variable= count to pass to csp_unsat_file.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
RS="${ROUNDINGSAT:-/home/pablo/projects/roundingsat/build/roundingsat}"
MODULE="$1"; CSP="$2"; OUT="$3"
CERTDIR="$ROOT/CSP/L2S/Backends/PB/Problems/certs"
DUMP="$ROOT/CSP/L2S/Backends/PB/Problems/_dump.lean"
mkdir -p "$CERTDIR"

cat > "$DUMP" <<EOF
import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Backends.PB.Serialize
import $MODULE
open CSP.L2S CSP.L2S.PB
def dumpCsp : IntCSP := $CSP
private def dumpNV : Nat := ((List.finRange (cspSig dumpCsp).nInt).map (fun i => (cspSig dumpCsp).width i)).sum + (cspSig dumpCsp).nBool + (cspSig dumpCsp).nAux
#eval IO.println dumpNV
#eval IO.println (toOPBString
  (((cspSig dumpCsp).monotonicity ++ EncConstr.combine (encodeCSP dumpCsp)).toArray.map PBConstr.toNatConstr) dumpNV)
EOF

cd "$ROOT"
lake env lean "$DUMP" 2>/dev/null > /tmp/gc_dump.out
NV="$(head -1 /tmp/gc_dump.out)"
tail -n +2 /tmp/gc_dump.out > "/tmp/$OUT.opb"

"$RS" "/tmp/$OUT.opb" --proof-log="/tmp/$OUT.pbp" 2>&1 | grep -q "^s UNSATISFIABLE" \
  || { echo "ERROR: roundingsat did not report UNSATISFIABLE for $CSP"; exit 1; }
veripb --elaborate "$CERTDIR/$OUT.pbp" "/tmp/$OUT.opb" "/tmp/$OUT.pbp" 2>&1 | grep -q "VERIFIED" \
  || { echo "ERROR: veripb failed to verify $CSP"; exit 1; }

rm -f "$DUMP"
echo "numVars=$NV  ->  $CERTDIR/$OUT.pbp"
