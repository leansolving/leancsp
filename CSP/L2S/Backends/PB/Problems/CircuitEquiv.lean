import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«31_circuit_equivalence»

namespace CSP.L2S.PB.CircuitEquiv

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for XOR circuit equivalence

`xor_equivalence` (`Tests/lean/31_circuit_equivalence.lean`) asks whether two
implementations of 2-input XOR ever disagree: a native `xor_all` gate vs. the
decomposition `(x ∧ ¬y) ∨ (¬x ∧ y)` (via `not_gate`/`and_all`/`or_all`), with a miter
`ne` on the two outputs.  Unsatisfiable — the circuits are equivalent.

The generic encoder maps each gate to its linear `{0,1}` facets (binary `xor_all`: the
4 parity facets; `not_gate`: `out + in = 1`; `and_all`/`or_all`: min/max facets) and the
miter to the aux-free `≠`, so the proof is one `csp_unsat` over the committed certificate
(`certs/xor_equivalence.pbp`); axioms clean.
-/

/-- **XOR equivalence.**  The native XOR gate and its AND/OR/NOT decomposition never
    disagree. -/
theorem xor_equivalence_unsat : ¬ xor_equivalence.isSatisfiableInt :=
  csp_unsat_file xor_equivalence 8 "certs/xor_equivalence.pbp"

end CSP.L2S.PB.CircuitEquiv
