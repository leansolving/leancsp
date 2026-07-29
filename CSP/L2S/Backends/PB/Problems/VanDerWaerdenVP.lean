import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«33_van_der_waerden»

namespace CSP.L2S.PB.VanDerWaerdenVP

open CSP.L2S CSP.L2S.PB

/-- `W(2,3)=9` CSP extended with full value precedence (encoded staircase `xⱼ ≤ j`). -/
def vp_vdw_2_3_9 : IntCSP := (vdw_csp 9).addConstraint (value_precedence 2)

/-- **Value-precedence-extended `W(2,3)=9` is UNSAT.** -/
theorem vp_vdw_2_3_9_unsat : ¬ vp_vdw_2_3_9.isSatisfiableInt :=
  csp_unsat_file vp_vdw_2_3_9 9 "certs/vdw_2_3_9_vp.pbp"

end CSP.L2S.PB.VanDerWaerdenVP
