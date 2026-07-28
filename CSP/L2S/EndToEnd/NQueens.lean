import CSP.L2S.Backends.PB.Problems.NQueensSBC

/-!
# End-to-end UNSAT via symmetry breaking — N-Queens

Recovers UNSAT of the **original** N-Queens CSPs from UNSAT of their *symmetry-broken*
extensions (kernel-checked PB certificates) via the verified horizontal-reflection SBC
(`Proofs/NQueensSB.lean`), using the bridge `CSP.L2S.unsat_of_sbc`.
-/

namespace CSP.L2S.EndToEnd.NQueens

open CSP.L2S CSP.L2S.PB CSP.L2S.PB.NQueensSBC

/-- **End-to-end: 2-Queens is unsolvable.** -/
theorem nqueens_2_unsat : ¬ (nqueens_csp 2).isSatisfiableInt :=
  unsat_of_sbc _ _
    (nqueens_sbc_is_symmetry_breaking 2 (by decide))
    sb_nqueens_2_unsat

/-- **End-to-end: 3-Queens is unsolvable.** -/
theorem nqueens_3_unsat : ¬ (nqueens_csp 3).isSatisfiableInt :=
  unsat_of_sbc _ _
    (nqueens_sbc_is_symmetry_breaking 3 (by decide))
    sb_nqueens_3_unsat

end CSP.L2S.EndToEnd.NQueens
