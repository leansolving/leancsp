import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«34_ramsey»

namespace CSP.L2S.PB.RamseyVP

open CSP.L2S CSP.L2S.PB

/-- `R(3,3)=6` CSP extended with full value precedence (encoded staircase `xⱼ ≤ j`). -/
def vp_ramsey_3_3_K6 : IntCSP := (ramsey_r33_csp 6).addConstraint (value_precedence 2)

/-- **Value-precedence-extended `R(3,3)=6` is UNSAT.** -/
theorem vp_ramsey_3_3_K6_unsat : ¬ vp_ramsey_3_3_K6.isSatisfiableInt :=
  csp_unsat_file vp_ramsey_3_3_K6 15 "certs/ramsey_3_3_vp.pbp"

end CSP.L2S.PB.RamseyVP
