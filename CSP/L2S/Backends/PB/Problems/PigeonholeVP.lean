import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.PigeonholeValuePrecedence

namespace CSP.L2S.PB.PigeonholeVP

open CSP.L2S CSP.L2S.PB

/-- 0-indexed PHP(3,2) extended with value precedence (encoded staircase `xⱼ ≤ j`). -/
def vp_php_3_2 : IntCSP := (Pigeonhole.php_sb 3 2).addConstraint (value_precedence 2)

/-- 0-indexed PHP(5,4) extended with value precedence. -/
def vp_php_5_4 : IntCSP := (Pigeonhole.php_sb 5 4).addConstraint (value_precedence 4)

/-- **Value-precedence-extended PHP(3,2) is UNSAT.** -/
theorem vp_php_3_2_unsat : ¬ vp_php_3_2.isSatisfiableInt :=
  csp_unsat_file vp_php_3_2 3 "certs/php_3_2_vp.pbp"

/-- **Value-precedence-extended PHP(5,4) is UNSAT.** -/
theorem vp_php_5_4_unsat : ¬ vp_php_5_4.isSatisfiableInt :=
  csp_unsat_file vp_php_5_4 15 "certs/php_5_4_vp.pbp"

end CSP.L2S.PB.PigeonholeVP
