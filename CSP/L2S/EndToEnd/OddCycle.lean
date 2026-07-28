import CSP.L2S.Backends.PB.Problems.OddCycleSBC
import CSP.L2S.Proofs.GraphColoringValuePrecedence

/-!
# End-to-end UNSAT via symmetry breaking — odd cycles

Odd cycles `C₅/C₇/C₉` are not 2-colourable. Recovered from UNSAT of the *symmetry-broken*
extensions (kernel-checked PB certificates) via the verified colour-fixing SBC
(`Proofs/GraphColoringSB.lean`, applied to the cycle as a graph), using `CSP.L2S.unsat_of_sbc`.
-/

namespace CSP.L2S.EndToEnd.OddCycle

open CSP.L2S CSP.L2S.PB CSP.L2S.PB.OddCycleSBC

/-- **End-to-end: `C₅` is not 2-colourable.** -/
theorem c5_2col_unsat : ¬ (graph_coloring_csp 5 c5_edges 2).isSatisfiableInt :=
  unsat_of_sbc _ _
    (graph_coloring_sbc_is_symmetry_breaking 5 2 (by decide) (by decide) c5_edges)
    sb_c5_2col_unsat

/-- **End-to-end: `C₇` is not 2-colourable.** -/
theorem c7_2col_unsat : ¬ (graph_coloring_csp 7 c7_edges 2).isSatisfiableInt :=
  unsat_of_sbc _ _
    (graph_coloring_sbc_is_symmetry_breaking 7 2 (by decide) (by decide) c7_edges)
    sb_c7_2col_unsat

/-- **End-to-end: `C₉` is not 2-colourable.** -/
theorem c9_2col_unsat : ¬ (graph_coloring_csp 9 c9_edges 2).isSatisfiableInt :=
  unsat_of_sbc _ _
    (graph_coloring_sbc_is_symmetry_breaking 9 2 (by decide) (by decide) c9_edges)
    sb_c9_2col_unsat

/-- **End-to-end via full value precedence: `C₅` is not 2-colourable.** -/
theorem c5_2col_unsat_via_value_precedence :
    ¬ (graph_coloring_csp 5 c5_edges 2).isSatisfiableInt :=
  graph_coloring_unsat_of_value_precedence 5 2 c5_edges vp_c5_2col_unsat

/-- **End-to-end via full value precedence: `C₇` is not 2-colourable.** -/
theorem c7_2col_unsat_via_value_precedence :
    ¬ (graph_coloring_csp 7 c7_edges 2).isSatisfiableInt :=
  graph_coloring_unsat_of_value_precedence 7 2 c7_edges vp_c7_2col_unsat

/-- **End-to-end via full value precedence: `C₉` is not 2-colourable.** -/
theorem c9_2col_unsat_via_value_precedence :
    ¬ (graph_coloring_csp 9 c9_edges 2).isSatisfiableInt :=
  graph_coloring_unsat_of_value_precedence 9 2 c9_edges vp_c9_2col_unsat

end CSP.L2S.EndToEnd.OddCycle
