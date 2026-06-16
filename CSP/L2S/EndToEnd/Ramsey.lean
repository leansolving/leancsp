import CSP.L2S.Backends.PB.Problems.RamseyVP
import CSP.L2S.Proofs.RamseyValuePrecedence

/-!
# End-to-end UNSAT via value precedence — Ramsey

`R(3,3) = 6`: every 2-colouring of `K₆`'s edges has a monochromatic triangle.  Recovered from
UNSAT of the value-precedence-extended CSP through `ramsey_unsat_of_value_precedence`.
-/

namespace CSP.L2S.EndToEnd.Ramsey

open CSP.L2S

/-- **End-to-end `R(3,3) = 6` via full value precedence.** -/
theorem ramsey_3_3_K6_unsat_via_value_precedence : ¬ (ramsey_r33_csp 6).isSatisfiableInt :=
  ramsey_unsat_of_value_precedence 6 PB.RamseyVP.vp_ramsey_3_3_K6_unsat

end CSP.L2S.EndToEnd.Ramsey
