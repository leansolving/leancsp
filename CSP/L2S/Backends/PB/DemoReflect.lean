import CSP.L2S.Backends.PB.Demo
import CSP.L2S.Backends.PB.Tactic

namespace CSP.L2S.PB.Demo

open CSP.L2S.PB

/-!
# PB backend — `csp_reflect_unsat` demonstration

Reproduces `Demo.lean`'s `formulaUnsat demoEncoding` through the
`csp_reflect_unsat` command instead of a hand-written `checkProof_sound` call:
the VeriPB kernel proof now lives in a committed file
(`proofs/demo3.kernel.pbp`) rather than an embedded string, and the command
discharges it via PBLean's reflection checker (a hand-built `Lean.ofReduceBool`
term).  Build-time cost is one native reflection eval; no external solver runs.
-/

-- Registers `demo3_formulaUnsat : formulaUnsat demoEncoding` from the committed proof.
csp_reflect_unsat demo3_formulaUnsat demoEncoding 9
  "CSP/L2S/Backends/PB/proofs/demo3.kernel.pbp"

/-- The command produced exactly the expected statement. -/
example : VeriPB.Reflect.formulaUnsat demoEncoding := demo3_formulaUnsat

end CSP.L2S.PB.Demo
