import CSP.L2S.Backends.PB.Problems.GraphColoringSBC

/-!
# End-to-end UNSAT via symmetry breaking — graph colouring

Recovers UNSAT of the **original** clique-colouring CSPs from UNSAT of their *symmetry-broken*
extensions (kernel-checked PB certificates) via the verified colour-fixing SBC
(`Proofs/GraphColoringSB.lean`), using the bridge `CSP.L2S.unsat_of_sbc`.
-/

namespace CSP.L2S.EndToEnd.GraphColoring

open CSP.L2S CSP.L2S.PB CSP.L2S.PB.GraphColoringSBC

/-- **End-to-end: `K₃` is not 2-colourable.** -/
theorem k3_2col_unsat :
    ¬ (graph_coloring_csp 3 k3_edges 2).isSatisfiableInt :=
  unsat_of_sbc _ _
    (sb_constraint_is_symmetry_breaking 3 2 (by decide) (by decide) k3_edges)
    extended_k3_2col_unsat

/-- **End-to-end: `K₄` is not 3-colourable.** -/
theorem k4_3col_unsat :
    ¬ (graph_coloring_csp 4 k4_edges 3).isSatisfiableInt :=
  unsat_of_sbc _ _
    (sb_constraint_is_symmetry_breaking 4 3 (by decide) (by decide) k4_edges)
    extended_k4_3col_unsat

end CSP.L2S.EndToEnd.GraphColoring
