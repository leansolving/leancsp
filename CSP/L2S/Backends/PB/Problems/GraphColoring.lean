import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«02_color»

namespace CSP.L2S.PB.GraphColoring

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for graph colouring

`k3_2col` colours the triangle **K₃** with two colours (the smallest
non-2-colourable graph) and `k4_3col` colours **K₄** with three colours; both
(`Tests/lean/02_color.lean`) give each vertex a colour variable over `{1,…,c}`
with a `not_equal u v` per edge, and both are unsatisfiable (a `c`-clique needs
`c+1` colours).

Each is discharged by a **single** `csp_unsat` application over its committed
kernel certificate — no per-problem signature, encoding, or bridge.  The generic
encoder turns every `not_equal` edge into the aux-free order encoding and the
bounds into the domain; `#print axioms` is `propext, Classical.choice, Quot.sound`
plus the two reflection axioms `Lean.ofReduceBool` / `Lean.trustCompiler` (no `sorryAx`).
-/

/-- **K₃ is not 2-colourable.** -/
theorem k3_2col_unsat : ¬ k3_2col.isSatisfiableInt :=
  csp_unsat_file k3_2col 3 "certs/k3.pbp"

/-- **K₄ is not 3-colourable.** -/
theorem k4_3col_unsat : ¬ k4_3col.isSatisfiableInt :=
  csp_unsat_file k4_3col 8 "certs/k4.pbp"

end CSP.L2S.PB.GraphColoring
