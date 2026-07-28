import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.GraphColoringSB

namespace CSP.L2S.PB.OddCycleSBC

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for *symmetry-broken* odd-cycle 2-colouring

An odd cycle `C_{2m+1}` is a graph, so the `GraphColoringSB` machinery applies verbatim: the cycle
(2 colours, a `not_equal` per edge) extended with the verified colour-fixing SBC `equals_const x₀ 0`.
Odd cycles are not 2-colourable; the original-cycle theorems are assembled in
`CSP/L2S/EndToEnd/OddCycle.lean`.
-/

/-- Edges of the cycle `C₅`. -/
def c5_edges : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

/-- Edges of the cycle `C₇`. -/
def c7_edges : List (Fin 7 × Fin 7) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0)]

/-- Edges of the cycle `C₉`. -/
def c9_edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 0)]

/-- `C₅` 2-colouring extended with the colour-fixing SBC `x₀ = 0`. -/
def sb_c5_2col : IntCSP := graph_coloring_sb 5 (by decide) c5_edges 2

/-- `C₇` 2-colouring extended with the colour-fixing SBC `x₀ = 0`. -/
def sb_c7_2col : IntCSP := graph_coloring_sb 7 (by decide) c7_edges 2

/-- `C₉` 2-colouring extended with the colour-fixing SBC `x₀ = 0`. -/
def sb_c9_2col : IntCSP := graph_coloring_sb 9 (by decide) c9_edges 2

/-- **Symmetry-broken: `C₅` is not 2-colourable.** -/
theorem sb_c5_2col_unsat : ¬ sb_c5_2col.isSatisfiableInt :=
  csp_unsat_file sb_c5_2col 5 "certs/c5_sbc.pbp"

/-- **Symmetry-broken: `C₇` is not 2-colourable.** -/
theorem sb_c7_2col_unsat : ¬ sb_c7_2col.isSatisfiableInt :=
  csp_unsat_file sb_c7_2col 7 "certs/c7_sbc.pbp"

/-- **Symmetry-broken: `C₉` is not 2-colourable.** -/
theorem sb_c9_2col_unsat : ¬ sb_c9_2col.isSatisfiableInt :=
  csp_unsat_file sb_c9_2col 9 "certs/c9_sbc.pbp"

/-- `C₅` 2-colouring extended with full value precedence. -/
def vp_c5_2col : IntCSP := (graph_coloring_csp 5 c5_edges 2).addConstraint (value_precedence 2)
/-- `C₇` 2-colouring extended with full value precedence. -/
def vp_c7_2col : IntCSP := (graph_coloring_csp 7 c7_edges 2).addConstraint (value_precedence 2)
/-- `C₉` 2-colouring extended with full value precedence. -/
def vp_c9_2col : IntCSP := (graph_coloring_csp 9 c9_edges 2).addConstraint (value_precedence 2)

/-- **Value-precedence-extended: `C₅` is not 2-colourable.** -/
theorem vp_c5_2col_unsat : ¬ vp_c5_2col.isSatisfiableInt :=
  csp_unsat_file vp_c5_2col 5 "certs/c5_vp.pbp"
/-- **Value-precedence-extended: `C₇` is not 2-colourable.** -/
theorem vp_c7_2col_unsat : ¬ vp_c7_2col.isSatisfiableInt :=
  csp_unsat_file vp_c7_2col 7 "certs/c7_vp.pbp"
/-- **Value-precedence-extended: `C₉` is not 2-colourable.** -/
theorem vp_c9_2col_unsat : ¬ vp_c9_2col.isSatisfiableInt :=
  csp_unsat_file vp_c9_2col 9 "certs/c9_vp.pbp"

end CSP.L2S.PB.OddCycleSBC
