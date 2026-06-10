import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«28_full_adder_verification»

namespace CSP.L2S.PB.FullAdder

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for full-adder circuit verification

`full_adder_verification` (`Tests/lean/28_full_adder_verification.lean`) asserts that the
full adder (`sum = a ⊕ b ⊕ cin` via a ternary `xor_all`, `cout` = majority via three
`and_gate`s feeding an `or_all`) *violates* its arithmetic specification
`a + b + cin = 2·cout + sum` (a `linear_ne`).  Unsatisfiable — the circuit is correct.

The generic encoder maps the ternary `xor_all` to the 8 facets of the parity polytope,
each `and_gate`/`or_all` to its min/max facets, and the negated specification to the
Big-M `≠` (one allocator-managed selector), so the proof is one `csp_unsat` over the
committed certificate (`certs/full_adder.pbp`); axioms clean.
-/

/-- **Full-adder correctness.**  The gate-level full adder always satisfies
    `a + b + cin = 2·cout + sum`. -/
theorem full_adder_correct_unsat : ¬ full_adder_verification.isSatisfiableInt :=
  csp_unsat_file full_adder_verification 9 "certs/full_adder.pbp"

end CSP.L2S.PB.FullAdder
