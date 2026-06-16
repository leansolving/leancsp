import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.NQueensSB

namespace CSP.L2S.PB.NQueensSBC

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for *symmetry-broken* N-Queens

`nqueens_csp n` (one row variable per column; `alldifferent` rows + `alldifferentOffset`
diagonals) extended with the verified horizontal-reflection SBC `x₀ < (n+1)/2`
(`sb_constraint`, proved a domain symmetry-breaking constraint in `Proofs/NQueensSB.lean`).
Adding the SBC keeps the small boards UNSAT; the original-board theorems are assembled in
`CSP/L2S/EndToEnd/NQueens.lean`.
-/

/-- 2-Queens extended with the reflection SBC. -/
def extended_nqueens_2 : IntCSP := extended_nqueens_csp 2 (by decide)

/-- 3-Queens extended with the reflection SBC. -/
def extended_nqueens_3 : IntCSP := extended_nqueens_csp 3 (by decide)

/-- **Symmetry-broken: 2-Queens is unsolvable.** -/
theorem extended_nqueens_2_unsat : ¬ extended_nqueens_2.isSatisfiableInt :=
  csp_unsat_file extended_nqueens_2 4 "certs/nqueens_2_sbc.pbp"

/-- **Symmetry-broken: 3-Queens is unsolvable.** -/
theorem extended_nqueens_3_unsat : ¬ extended_nqueens_3.isSatisfiableInt :=
  csp_unsat_file extended_nqueens_3 12 "certs/nqueens_3_sbc.pbp"

end CSP.L2S.PB.NQueensSBC
