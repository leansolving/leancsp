import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«33_van_der_waerden»

namespace CSP.L2S.PB.VanDerWaerden

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for van der Waerden `W(2,3) ≤ 9`

`vdw_2_3_9` (`Tests/lean/33_van_der_waerden.lean`) 2-colours `{1,…,9}` avoiding a
monochromatic 3-term arithmetic progression — infeasible, since `W(2,3) = 9`.  Each
AP is a `schur_triple` (not-all-equal) constraint; the generic encoder discharges
it, so the proof is one `csp_unsat` over the committed certificate
(`certs/vdw_2_3_9.pbp`); axioms clean.
-/

/-- **`W(2,3) ≤ 9`: every 2-colouring of `{1,…,9}` has a monochromatic 3-AP.** -/
theorem vdw_2_3_9_unsat : ¬ vdw_2_3_9.isSatisfiableInt :=
  csp_unsat_file vdw_2_3_9 9 "certs/vdw_2_3_9.pbp"

end CSP.L2S.PB.VanDerWaerden
