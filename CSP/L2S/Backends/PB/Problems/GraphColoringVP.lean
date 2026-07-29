import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Backends.PB.Problems.GraphColoringSBC

namespace CSP.L2S.PB.GraphColoringVP

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — UNSAT for *value-precedence*-extended clique colouring

`K₃`/2-colouring and `K₄`/3-colouring extended with the full Law–Lee `value_precedence`
constraint (encoded as the sound staircase `xⱼ ≤ j`).  Original-graph theorems are assembled in
`CSP/L2S/EndToEnd/GraphColoring.lean` via `graph_coloring_unsat_of_value_precedence`.
-/

/-- `K₃`/2-colouring extended with value precedence. -/
def vp_k3_2col : IntCSP :=
  (graph_coloring_csp 3 GraphColoringSBC.k3_edges 2).addConstraint (value_precedence 2)

/-- `K₄`/3-colouring extended with value precedence. -/
def vp_k4_3col : IntCSP :=
  (graph_coloring_csp 4 GraphColoringSBC.k4_edges 3).addConstraint (value_precedence 3)

/-- **Value-precedence-extended `K₃` is not 2-colourable.** -/
theorem vp_k3_2col_unsat : ¬ vp_k3_2col.isSatisfiableInt :=
  csp_unsat_file vp_k3_2col 3 "certs/k3_vp.pbp"

/-- **Value-precedence-extended `K₄` is not 3-colourable.** -/
theorem vp_k4_3col_unsat : ¬ vp_k4_3col.isSatisfiableInt :=
  csp_unsat_file vp_k4_3col 8 "certs/k4_vp.pbp"

end CSP.L2S.PB.GraphColoringVP
