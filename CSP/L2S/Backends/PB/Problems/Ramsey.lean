import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«34_ramsey»

namespace CSP.L2S.PB.Ramsey

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for Ramsey `R(3,3) ≤ 6`

`ramsey_3_3_K6` (`Tests/lean/34_ramsey.lean`) 2-colours the edges of `K₆` avoiding a
monochromatic triangle — infeasible, since `R(3,3) = 6`.  Each triangle is a
`schur_triple` (not-all-equal) over its three edge variables; the generic encoder
discharges it, so the proof is one `csp_unsat` over the committed certificate
(`certs/ramsey_3_3.pbp`); axioms clean.
-/

/-- **`R(3,3) ≤ 6`: every 2-colouring of `K₆` has a monochromatic triangle.** -/
theorem ramsey_3_3_K6_unsat : ¬ ramsey_3_3_K6.isSatisfiableInt :=
  csp_unsat_file ramsey_3_3_K6 15 "certs/ramsey_3_3.pbp"

end CSP.L2S.PB.Ramsey
