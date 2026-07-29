import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«32_circuit_at_least»

namespace CSP.L2S.PB.Circuit

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for the majority-of-3 circuit

`at_least_k_satisfies_circuit_csp majority3_circuit 2` (`Tests/lean/32_circuit_at_least.lean`)
asks: is there an input with at least 2 of `{A,B,C}` set on which the 3-input majority
circuit (three `and_all` gates feeding an `or_all`, i.e. the full-adder CARRY) outputs `0`?
Unsatisfiable — `≥ 2` inputs force `CARRY = 1`, the carry-correctness property.

The generic encoder maps each gate to its linear `{0,1}` facets (`and_all`:
`out ≤ each input`, `out ≥ Σ − (n−1)`; `or_all`: dual) and `at_least_k`/`ne_const` to
their linear forms, so the proof is one `csp_unsat` over the committed certificate
(`certs/circuit_majority3.pbp`); axioms clean.
-/

/-- **Majority-of-3 carry correctness.**  The majority circuit cannot output `0` when at
    least two of its three inputs are `1`. -/
theorem circuit_majority3_unsat :
    ¬ (at_least_k_satisfies_circuit_csp majority3_circuit 2).isSatisfiableInt :=
  csp_unsat_file (at_least_k_satisfies_circuit_csp majority3_circuit 2) 7
    "certs/circuit_majority3.pbp"

end CSP.L2S.PB.Circuit
