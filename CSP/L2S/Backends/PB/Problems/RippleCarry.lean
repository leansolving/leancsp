import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«29_ripple_carry_adder»

namespace CSP.L2S.PB.RippleCarry

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for a 4-bit ripple-carry adder

`ripple_carry_adder_4bit` (`Tests/lean/29_ripple_carry_adder.lean`) chains four gate-level
full adders (each a ternary `xor_all` for the sum bit plus three `and_gate`s and an
`or_all` for the carry) and asserts the adder *violates* its arithmetic specification
`A + B = Σ 2ⁱ·sᵢ + 16·cout` (a `linear_ne`, with carry-in fixed by `eq_const`).
Unsatisfiable — the adder is correct.

The generic encoder maps every gate to its linear `{0,1}` facets (ternary `xor_all`:
the 8 parity-polytope facets per stage) and the negated specification to the Big-M `≠`
(one allocator-managed selector), so the proof is one `csp_unsat` over the committed
certificate (`certs/ripple_carry_4bit.pbp`); axioms clean.
-/

/-- **Ripple-carry correctness.**  The 4-bit gate-level ripple-carry adder always
    satisfies `A + B = result`. -/
theorem ripple_carry_4bit_correct_unsat : ¬ ripple_carry_adder_4bit.isSatisfiableInt :=
  csp_unsat_file ripple_carry_adder_4bit 30 "certs/ripple_carry_4bit.pbp"

end CSP.L2S.PB.RippleCarry
