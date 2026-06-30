#!/usr/bin/env bash
# Generate an (untrusted) colouring witness for the *extended* Schur CSP
# `Schur.extended_schur n h c` (the symmetry-broken model, x₀ = 0), and commit it
# under CSP/L2S/EndToEnd/sols/<out>.sol as a space-separated list of n colours.
#
# This is the SAT-direction analog of scripts/gen_cert.sh.  The MiniZinc model below
# mirrors `(Schur.schur_sb n c).addConstraint (value_precedence c)` (0-indexed: variable i
# is the integer i+1; triples are i ≤ j with k = i+j+1 < n; "not all equal"; plus the
# full Law–Lee value-precedence SBC matching `patternHolds`: any colour ≥ 1 at position j
# is preceded by its predecessor colour somewhere before j).  Value-precedence is the
# *uniform* SBC used across all Schur instances in this experiment; it implies x[0] = 0.
# The witness is untrusted: `csp_sat_file` re-checks it in the Lean kernel, so a wrong
# model here only fails to elaborate — it can never produce an unsound theorem.
#
# Usage: scripts/gen_sol.sh <n> <c> <out> [solver]
#   <n>       number of integers {1,…,n}
#   <c>       number of colours
#   <out>     witness base name, e.g. schur_c2_n4  (-> sols/schur_c2_n4.sol)
#   [solver]  MiniZinc solver (default: gecode; use chuffed for the larger instances)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
N="$1"; C="$2"; OUT="$3"; SOLVER="${4:-gecode}"
SOLDIR="$ROOT/CSP/L2S/EndToEnd/sols"
MZN="/tmp/$OUT.mzn"
mkdir -p "$SOLDIR"

cat > "$MZN" <<EOF
int: n = $N;
int: c = $C;
array[0..n-1] of var 0..c-1: x;
% full value-precedence SBC (matches patternHolds; implies x[0] = 0):
constraint forall(j in 0..n-1)( x[j] >= 1 -> exists(i in 0..j-1)(x[i] = x[j] - 1) );
constraint forall(i in 0..n-1, j in i..n-1 where i + j + 1 <= n - 1)(
  not (x[i] = x[j] /\\ x[j] = x[i + j + 1]));
solve satisfy;
output [ show(x[i]) ++ (if i < n - 1 then " " else "" endif) | i in 0..n-1 ];
EOF

OUTLINE="$(minizinc --solver "$SOLVER" "$MZN" | head -1)"
if [ -z "$OUTLINE" ] || echo "$OUTLINE" | grep -q "UNSATISFIABLE\|=====UNSATISFIABLE"; then
  echo "ERROR: solver $SOLVER found no colouring for n=$N c=$C"; exit 1
fi
echo "$OUTLINE" > "$SOLDIR/$OUT.sol"
echo "wrote $SOLDIR/$OUT.sol  ($(wc -w < "$SOLDIR/$OUT.sol") colours)"
