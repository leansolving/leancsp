import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«08_queens»

namespace CSP.L2S.PB.BlockedQueens

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for a blocked 4-Queens instance

4-Queens is satisfiable, so blocking is a genuine restriction: `blockedQueens4` adds to
the corpus `nqueens_csp 4` model a `ne_const` per row forbidding column 1.  Unsatisfiable
by a column pigeonhole: four all-different columns from the three non-1 values.

The generic encoder maps `alldifferent` to per-value cardinality, each diagonal
`alldifferentOffset` to its pairwise Big-M `≠` expansion, and the blocks to aux-free
`≠`-const, so the proof is one `csp_unsat` over the committed certificate
(`certs/blocked_queens_4.pbp`); axioms clean.
-/

/-- The corpus 4-queens model with column 1 forbidden in every row. -/
def blockedQueens4 : IntCSP :=
  (nqueens_csp 4).addConstraints
    [not_equals_const (⟨0, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
     not_equals_const (⟨1, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
     not_equals_const (⟨2, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
     not_equals_const (⟨3, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1]

/-- **Blocked 4-Queens is unsatisfiable.** -/
theorem blocked_queens_4_unsat : ¬ blockedQueens4.isSatisfiableInt :=
  csp_unsat_file blockedQueens4 24 "certs/blocked_queens_4.pbp"

end CSP.L2S.PB.BlockedQueens
