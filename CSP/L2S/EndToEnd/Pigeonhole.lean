import CSP.L2S.Backends.PB.Problems.PigeonholeVP

/-!
# End-to-end UNSAT via value precedence — Pigeonhole

`k+1` pigeons cannot injectively occupy `k` holes.  Recovered from UNSAT of the
value-precedence-extended (0-indexed) pigeonhole CSP through `php_unsat_of_value_precedence`.
(Pigeonhole is *easy* for cutting planes, so value precedence is a correctness/breadth
demonstrator here, not a solving-time win.)
-/

namespace CSP.L2S.EndToEnd.Pigeonhole

open CSP.L2S

/-- **End-to-end PHP(3,2) via full value precedence.** -/
theorem php_3_2_unsat_via_value_precedence : ¬ (_root_.Pigeonhole.php_csp 3 2).isSatisfiableInt :=
  _root_.Pigeonhole.php_unsat_of_value_precedence 3 2 PB.PigeonholeVP.vp_php_3_2_unsat

/-- **End-to-end PHP(5,4) via full value precedence.** -/
theorem php_5_4_unsat_via_value_precedence : ¬ (_root_.Pigeonhole.php_csp 5 4).isSatisfiableInt :=
  _root_.Pigeonhole.php_unsat_of_value_precedence 5 4 PB.PigeonholeVP.vp_php_5_4_unsat

end CSP.L2S.EndToEnd.Pigeonhole
