import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.DemoGeneric
import Mathlib.Tactic.FinCases

namespace CSP.L2S.PB.DemoHomogeneous

open CSP.L2S.PB.DemoGeneric (demoSig demoLin encode_eq)

/-!
# PB backend — end-to-end UNSAT for a *real* `HomogeneousCSP` (PLAN.md M5)

`DemoGeneric.lean` runs the verified spine on a hand-written `CSPSig` + `lin`
list.  This file closes the loop: the *same* UNSAT instance is now stated as an
honest `HomogeneousCSP` — three integer variables bounded to `{0,1,2,3}` with the
constraints `x+y+z ≤ 2` and `x+y+z ≥ 5` (the latter as a `linear_le` with negated
coefficients) — and `unsat_of_pb` (Adapter.lean) discharges
`¬ demoHomCSP.isSatisfiable` from the committed PB certificate
(`Demo.demo_formulaUnsat`), with the `bound` / `linear_le` bridge lemmas supplying
the in-domain and linear facts.  No hand-wired order-encoding soundness.

The `Fin csp.num_vars` `OfNat`-synthesis friction (MEM_002 #12) is sidestepped by
giving `demoHomCSP` a concrete `num_vars := 3` and reusing the already-`Fin 3`-typed
`demoLin`; every `Fin` literal stays concrete and unifies with `Fin demoHomCSP.num_vars`
by defeq at the `unsat_of_pb` application.
-/

/-- The three-variable demo as a genuine `HomogeneousCSP`:
    `x, y, z ∈ {0,1,2,3}`, `x+y+z ≤ 2`, and `x+y+z ≥ 5` (the latter encoded as
    `−x−y−z ≤ −5`, staying inside the `bound`+`linear_le` fragment). -/
def demoHomCSP : HomogeneousCSP where
  num_vars := 3
  constraints :=
    [ bound 0 0 3, bound 1 0 3, bound 2 0 3,
      linear_le ⟨#[0, 1, 2], rfl⟩ ⟨#[1, 1, 1], rfl⟩ 2,
      linear_le ⟨#[0, 1, 2], rfl⟩ ⟨#[-1, -1, -1], rfl⟩ (-5) ]

/-- **End-to-end theorem.** The genuine `HomogeneousCSP` `demoHomCSP` is
    unsatisfiable — discharged by `unsat_of_pb` from the committed PB certificate,
    with no hand-wired soundness step. -/
theorem demoHom_unsat : ¬ demoHomCSP.isSatisfiable := by
  refine unsat_of_pb demoHomCSP (fun _ => 0) (fun _ => 3) ?_ ?_ demoLin ?_ ?_
  · -- the bounds are well-formed: `0 ≤ 3`
    intro i; norm_num
  · -- every variable's `bound i 0 3` is in the constraint list
    intro i
    fin_cases i
    · exact .head _
    · exact .tail _ (.head _)
    · exact .tail _ (.tail _ (.head _))
  · -- the two linear `≤` facts follow from any solution, via `linear_le_sat`
    intro a hsol c hc
    have b1 := linear_le_sat _ _ _ a (hsol _ (.tail _ (.tail _ (.tail _ (.head _)))))
    have b2 := linear_le_sat _ _ _ a (hsol _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    fin_cases hc
    · exact b1
    · exact b2
  · -- the PB order encoding of `(toCSPSig demoHomCSP …, demoLin)` is `formulaUnsat`
    show VeriPB.Reflect.formulaUnsat
      ((encodeLinear demoSig demoLin).toArray.map PBConstr.toNatConstr)
    rw [encode_eq]
    exact Demo.demo_formulaUnsat

end CSP.L2S.PB.DemoHomogeneous
