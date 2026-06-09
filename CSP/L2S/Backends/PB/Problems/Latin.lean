import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«07_latin_squares»

namespace CSP.L2S.PB.Latin

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for a Latin square with contradictory givens

The binary-encoded Latin square of `Tests/lean/07_latin_squares.lean`.  The corpus
`latin_square_csp n` uses `n³` Boolean indicators with `sum_eq … = 1` families (one
value per cell, each value once per row/column).  `latin_2_contradictory` adds two
clues pinning both value-indicators of cell `(0,0)` to `1` ("the cell is both value 1
and value 2"), contradicting that cell's `sum_eq`.  Both `sum_eq` and `equals_const`
are supported, so the proof is one `csp_unsat` over the committed certificate
(`certs/latin_2.pbp`); axioms clean.
-/

/-- The contradictory-clue instance: the corpus 2×2 binary Latin square
    (`latin_square_csp 2`) with two clues pinning cell `(0,0)`'s value-1 and value-2
    indicators (variables 0 and 1) *both* to `1`, violating cell `(0,0)`'s `sum_eq`. -/
def latin_2_contradictory : IntCSP :=
  (latin_square_csp 2).addConstraints
    [equals_const ⟨0, by decide⟩ 1, equals_const ⟨1, by decide⟩ 1]

/-- **The contradictory-clue 2×2 Latin square is unsatisfiable.** -/
theorem latin_2_contradictory_unsat : ¬ latin_2_contradictory.isSatisfiableInt :=
  csp_unsat_file latin_2_contradictory 8 "certs/latin_2.pbp"

end CSP.L2S.PB.Latin
