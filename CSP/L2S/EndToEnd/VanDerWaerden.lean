import CSP.L2S.Backends.PB.Problems.VanDerWaerdenVP
import CSP.L2S.Proofs.VanDerWaerdenValuePrecedence

/-!
# End-to-end UNSAT via value precedence — Van der Waerden

`W(2,3) = 9`: `{1,…,9}` cannot be 2-coloured without a monochromatic 3-AP.  Recovered from UNSAT
of the value-precedence-extended CSP through `vdw_unsat_of_value_precedence`.
-/

namespace CSP.L2S.EndToEnd.VanDerWaerden

open CSP.L2S

/-- **End-to-end `W(2,3) = 9` via full value precedence.** -/
theorem vdw_2_3_9_unsat_via_value_precedence : ¬ (vdw_csp 9).isSatisfiableInt :=
  vdw_unsat_of_value_precedence 9 PB.VanDerWaerdenVP.vp_vdw_2_3_9_unsat

end CSP.L2S.EndToEnd.VanDerWaerden
