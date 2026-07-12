import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«35_pigeonhole»

namespace CSP.L2S.PB.Pigeonhole

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the pigeonhole corpus

The corpus CSPs `php_3_2`, `php_5_4`, `php_7_6`, `php_9_8`
(`Tests/lean/35_pigeonhole.lean`) — `k+1` pigeons into `k` holes, no two sharing —
are each proved `¬ isSatisfiableInt` by a **single** application of the generic
`csp_unsat` theorem (`GenericEncode.lean`): no per-problem signature, scope,
encoding, or soundness bridge.  The only per-problem datum is the committed
VeriPB kernel certificate under `certs/`, regenerated against the canonical
encoder by `scripts/gen_cert.sh` and loaded at compile time (`include_str`),
kernel-checked through PBLean's reflection checker.

`#print axioms` for each is `propext, Classical.choice, Quot.sound` + the two
reflection axioms `Lean.ofReduceBool` / `Lean.trustCompiler` (no `sorryAx`).
-/

/-- **Pigeonhole `php_3_2`** (three pigeons, two holes) is unsatisfiable. -/
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiableInt :=
  csp_unsat_file php_3_2 3 "certs/php_3_2.pbp"

/-- **Pigeonhole `php_5_4`** (five pigeons, four holes) is unsatisfiable. -/
theorem php_5_4_unsat : ¬ php_5_4.isSatisfiableInt :=
  csp_unsat_file php_5_4 15 "certs/php_5_4.pbp"

/-- **Pigeonhole `php_7_6`** (seven pigeons, six holes) is unsatisfiable. -/
theorem php_7_6_unsat : ¬ php_7_6.isSatisfiableInt :=
  csp_unsat_file php_7_6 35 "certs/php_7_6.pbp"

/-- **Pigeonhole `php_9_8`** (nine pigeons, eight holes) is unsatisfiable. -/
theorem php_9_8_unsat : ¬ php_9_8.isSatisfiableInt :=
  csp_unsat_file php_9_8 63 "certs/php_9_8.pbp"

end CSP.L2S.PB.Pigeonhole
