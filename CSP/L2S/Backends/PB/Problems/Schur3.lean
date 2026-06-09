import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«11_schur»

namespace CSP.L2S.PB.Schur3

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for Schur number `S(3) < 14`

`schur_3_14` (`Tests/lean/11_schur.lean`) 3-colours `{1,…,14}` with no monochromatic
`x + y = z` — infeasible, since the Schur number `S(3) = 13`.  Each forbidden triple
is a `schur_triple` (not-all-equal) constraint, discharged by the generic encoder,
so the proof is one `csp_unsat` over the committed certificate
(`certs/schur_3_14.pbp`); axioms clean.
-/

/-- **`S(3) < 14`: `{1,…,14}` has no sum-free 3-colouring.** -/
theorem schur_3_14_unsat : ¬ schur_3_14.isSatisfiableInt :=
  csp_unsat_file schur_3_14 28 "certs/schur_3_14.pbp"

end CSP.L2S.PB.Schur3
