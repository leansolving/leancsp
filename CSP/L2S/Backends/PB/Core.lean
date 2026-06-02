/-
PB (pseudo-Boolean) verified backend — umbrella / bridge-API anchor.

Confirms that leancsp (`HomogeneousCSP`, with Mathlib) and PBLean
(`VeriPB.*`, Mathlib-free) co-compile on the shared Lean 4.30.0 toolchain,
and pins down the exact PBLean symbols the UNSAT bridge composes with:

  * `Sat.PB.Constr` — a pseudo-Boolean constraint `Σ aᵢ·lᵢ ≥ degree`.
  * `VeriPB.Reflect.checkProofBool : Array Constr → Nat → String → Bool`.
  * `VeriPB.Reflect.checkProof_sound` — soundness: a `true` check yields
    `formulaUnsat` of the Lean-side constraint array (the `.opb` file is
    outside the trust base; the proof is consumed as a raw `String`).

The encoder (PLAN.md M2/M3) targets `formulaUnsat (Array Sat.PB.Constr)`.
-/
import CSP.L2S.Core
import VeriPB.Tactic.Sat.Reflect

namespace CSP.L2S.PB

open Sat.PB (Constr Literal)

/-- The bridge contract we build on: a verified VeriPB proof string makes the
    Lean-side PB constraint array unsatisfiable. -/
example (cs : Array Constr) (numVars : Nat) (proof : String)
    (h : VeriPB.Reflect.checkProofBool cs numVars proof = true) :
    VeriPB.Reflect.formulaUnsat cs :=
  VeriPB.Reflect.checkProof_sound cs numVars proof h

/-- Smoke check: both type families are usable together in one module. -/
example (_csp : HomogeneousCSP) (c : Constr) : Nat := c.degree

end CSP.L2S.PB
