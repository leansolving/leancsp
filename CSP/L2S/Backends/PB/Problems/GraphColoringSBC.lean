import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.GraphColoringSB

namespace CSP.L2S.PB.GraphColoringSBC

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for *symmetry-broken* graph colouring

The clique `Kₙ` (every vertex over colours `{0,…,c-1}`, a `not_equal` per edge) extended with
the verified colour-fixing SBC `equals_const x₀ 0` (`sb_constraint`, proved a domain
symmetry-breaking constraint in `Proofs/GraphColoringSB.lean`).  Adding the SBC keeps the clique
UNSAT (`Kₙ` needs `n` colours); the generic encoder discharges the `equals_const` facet.  The
original-graph theorems are assembled in `CSP/L2S/EndToEnd/GraphColoring.lean`.
-/

/-- Edges of the triangle `K₃`. -/
def k3_edges : List (Fin 3 × Fin 3) := [(0, 1), (0, 2), (1, 2)]

/-- Edges of `K₄`. -/
def k4_edges : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- `K₃`/2-colouring extended with the colour-fixing SBC `x₀ = 0`. -/
def extended_k3_2col : IntCSP := extended_graph_coloring_csp 3 (by decide) k3_edges 2

/-- `K₄`/3-colouring extended with the colour-fixing SBC `x₀ = 0`. -/
def extended_k4_3col : IntCSP := extended_graph_coloring_csp 4 (by decide) k4_edges 3

/-- **Symmetry-broken: `K₃` is not 2-colourable** (with `x₀` fixed). -/
theorem extended_k3_2col_unsat : ¬ extended_k3_2col.isSatisfiableInt :=
  csp_unsat_file extended_k3_2col 3 "certs/k3_sbc.pbp"

/-- **Symmetry-broken: `K₄` is not 3-colourable** (with `x₀` fixed). -/
theorem extended_k4_3col_unsat : ¬ extended_k4_3col.isSatisfiableInt :=
  csp_unsat_file extended_k4_3col 8 "certs/k4_sbc.pbp"

end CSP.L2S.PB.GraphColoringSBC
