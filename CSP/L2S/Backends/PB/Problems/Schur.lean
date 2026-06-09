import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«11_schur»

namespace CSP.L2S.PB.Schur

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for Schur number `S(2) < 5`

`schur_2_5` (`Tests/lean/11_schur.lean`) 2-colours `{1,…,5}` with no monochromatic
`x + y = z` — infeasible, since the Schur number `S(2) = 4`.  Each forbidden triple
is a `schur_triple` (not-all-equal) constraint; the generic encoder discharges it,
so the proof is one `csp_unsat` over the committed certificate
(`certs/schur_2_5.pbp`); axioms clean.
-/

/-- **`S(2) < 5`: `{1,…,5}` has no sum-free 2-colouring.** -/
theorem schur_2_5_unsat : ¬ schur_2_5.isSatisfiableInt :=
  csp_unsat_file schur_2_5 5 "certs/schur_2_5.pbp"

end CSP.L2S.PB.Schur
