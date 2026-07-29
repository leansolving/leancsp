import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«08_queens»

namespace CSP.L2S.PB.NQueens

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for `nqueens_csp 2` and `nqueens_csp 3`

`nqueens_csp n` (`Tests/lean/08_queens.lean`) places `n` queens, one per row: columns
all-different plus the two diagonal `alldifferentOffset` constraints.  For `n = 2, 3`
there is no solution.

The generic encoder maps each `alldifferentOffset` to its pairwise Big-M `≠` expansion
(one allocator-managed selector per pair) and `alldifferent` to per-value cardinality, so
each proof is one `csp_unsat` over its committed certificate; axioms clean.
-/

/-- **2-Queens is unsatisfiable.** -/
theorem nqueens_2_unsat : ¬ (nqueens_csp 2).isSatisfiableInt :=
  csp_unsat_file (nqueens_csp 2) 4 "certs/nqueens_2.pbp"

/-- **3-Queens is unsatisfiable.** -/
theorem nqueens_3_unsat : ¬ (nqueens_csp 3).isSatisfiableInt :=
  csp_unsat_file (nqueens_csp 3) 12 "certs/nqueens_3.pbp"

end CSP.L2S.PB.NQueens
