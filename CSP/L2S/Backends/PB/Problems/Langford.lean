import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«10_langford_simple»

namespace CSP.L2S.PB.Langford

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for Langford's problem `L(2,2)`

`langford_2n_csp 2` (`Tests/lean/10_langford_simple.lean`) asks for a Langford
sequence on `{1,1,2,2}` — known infeasible (`L(2,n)` exists iff `n ≡ 0,3 mod 4`).
It combines `alldifferent`, `bound`, and a `linear_eq` position constraint, all
supported by the generic encoder, so the proof is one `csp_unsat` over the
committed certificate (`certs/langford_2_2.pbp`); axioms clean.
-/

/-- **Langford `L(2,2)` is infeasible.** -/
theorem langford_2_2_unsat : ¬ (langford_2n_csp 2).isSatisfiableInt :=
  csp_unsat_file (langford_2n_csp 2) 12 "certs/langford_2_2.pbp"

end CSP.L2S.PB.Langford
