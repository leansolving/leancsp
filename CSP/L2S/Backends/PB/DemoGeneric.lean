import CSP.L2S.Backends.PB.Extend
import CSP.L2S.Backends.PB.Demo
import Mathlib.Tactic.FinCases

namespace CSP.L2S.PB.DemoGeneric

open CSP.L2S.PB

/-!
# PB backend — `Demo.demo_unsat` re-derived through the generic spine

`Demo.lean` proves its UNSAT result with a *hand-wired* order-encoding soundness
(`demoVal`, `le_sat`, `ge_sat`).  Here we obtain the same result from the generic
`csp_unsat_of_linear`, validating that the encoder reproduces the hand-built
`demoEncoding` exactly (so the committed PB certificate still applies) and that
the spine subsumes the hand proof.
-/

/-- The demo signature: three integer variables, each with domain `{0,1,2,3}`. -/
def demoSig : CSPSig where
  nInt := 3
  nBool := 0
  nAux := 0
  values := fun _ => [0, 1, 2, 3]
  sorted := by intro _; decide
  nonempty := by intro _; decide

/-- The demo's two linear constraints: `x+y+z ≤ 2` and `-(x+y+z) ≤ -5`
    (i.e. `x+y+z ≥ 5`). -/
def demoLin : List (List (Int × Fin 3) × Int) :=
  [([(1, 0), (1, 1), (1, 2)], 2), ([(-1, 0), (-1, 1), (-1, 2)], -5)]

/-- The generic encoder reproduces the hand-built `demoEncoding` byte-for-byte. -/
theorem encode_eq : (encodeLinear demoSig demoLin).toArray.map PBConstr.toNatConstr
    = Demo.demoEncoding := by
  rw [← Array.toList_inj]
  simp only [Array.toList_map, List.toList_toArray]
  rfl

/-- `Demo.demo_unsat`, re-derived through the **generic** spine: the committed PB
    certificate (`Demo.demo_formulaUnsat`) is transported across `encode_eq`, then
    `csp_unsat_of_linear` discharges the integer goal — no hand-wired soundness. -/
theorem demo_unsat_generic :
    ¬ ∃ x y z : Fin 4, x.val + y.val + z.val ≤ 2 ∧ x.val + y.val + z.val ≥ 5 := by
  have hunsat : VeriPB.Reflect.formulaUnsat
      ((encodeLinear demoSig demoLin).toArray.map PBConstr.toNatConstr) := by
    rw [encode_eq]; exact Demo.demo_formulaUnsat
  have hgen := csp_unsat_of_linear demoSig demoLin hunsat
  rintro ⟨x, y, z, hle, hge⟩
  apply hgen
  refine ⟨fun i => [(x.val : Int), y.val, z.val].getD i.val 0, ?_, ?_⟩
  · -- every coordinate lands in {0,1,2,3}
    intro i
    have hx := x.isLt; have hy := y.isLt; have hz := z.isLt
    fin_cases i <;> simp <;> omega
  · -- the two linear constraints hold
    intro c hc
    have hx := x.isLt; have hy := y.isLt; have hz := z.isLt
    fin_cases hc <;> simp [demoLin] <;> omega

end CSP.L2S.PB.DemoGeneric
