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
def extended_c5_2col : IntCSP := extended_graph_coloring_csp 5 (by decide) c5_edges 2

/-- `C₇` 2-colouring extended with the colour-fixing SBC `x₀ = 0`. -/
def extended_c7_2col : IntCSP := extended_graph_coloring_csp 7 (by decide) c7_edges 2

/-- `C₉` 2-colouring extended with the colour-fixing SBC `x₀ = 0`. -/
def extended_c9_2col : IntCSP := extended_graph_coloring_csp 9 (by decide) c9_edges 2

/-- **Symmetry-broken: `C₅` is not 2-colourable.** -/
theorem extended_c5_2col_unsat : ¬ extended_c5_2col.isSatisfiableInt :=
  csp_unsat_file extended_c5_2col 5 "certs/c5_sbc.pbp"

/-- **Symmetry-broken: `C₇` is not 2-colourable.** -/
theorem extended_c7_2col_unsat : ¬ extended_c7_2col.isSatisfiableInt :=
  csp_unsat_file extended_c7_2col 7 "certs/c7_sbc.pbp"

/-- **Symmetry-broken: `C₉` is not 2-colourable.** -/
theorem extended_c9_2col_unsat : ¬ extended_c9_2col.isSatisfiableInt :=
  csp_unsat_file extended_c9_2col 9 "certs/c9_sbc.pbp"

end CSP.L2S.PB.OddCycleSBC
