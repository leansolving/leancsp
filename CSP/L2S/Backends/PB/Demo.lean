import CSP.L2S.Backends.PB.Core

namespace CSP.L2S.PB.Demo

open Sat.PB

/-!
# PB backend — smallest end-to-end UNSAT demo (PLAN.md M3, Appendix A)

This is the thin vertical slice through the *entire* pipeline, proving a real
Lean theorem from a real pseudo-Boolean certificate:

  Lean order encoding  ──serialize──▶  .opb
        │                                 │
        │                          RoundingSat (external)
        │                                 ▼
        │                          VeriPB raw proof
        │                                 │
        │                       veripb --elaborate (external)
        │                                 ▼
        │                          VeriPB kernel proof  (embedded below as a String)
        ▼                                 │
  demoEncoding : Array Constr  ──PBLean checkProofBool (native_decide)──▶  formulaUnsat
        │                                                                      │
        └──────────────── order-encoding soundness (this file) ───────────────┘
                                          ▼
            ¬ ∃ x y z : Fin 4, x+y+z ≤ 2 ∧ x+y+z ≥ 5

The problem: three CSP variables `x, y, z ∈ {0,1,2,3}` with the (jointly
unsatisfiable) constraints `x+y+z ≤ 2` and `x+y+z ≥ 5`.  We order-encode each
variable with three threshold bits `t_v^j ⟺ (v ≤ j)` (`gap = 1`, `maxVal = 3`,
so `intValue_v = 3 − Σⱼ t_v^j`), giving 9 Boolean variables (`x:0,1,2  y:3,4,5
z:6,7,8`), 6 monotonicity clauses, and the two linear constraints rewritten via
the substitution identity (PLAN §5):
  `x+y+z ≤ 2  ⟹  Σ tⱼ ≥ 7`     and     `x+y+z ≥ 5  ⟹  Σ ¬tⱼ ≥ 5`.

Trust boundary: RoundingSat, veripb, and the `.opb`/serializer are **untrusted**
— if any is wrong, `checkProofBool` returns `false` and `demo_formulaUnsat`
fails to elaborate.  Only PBLean's checker and the soundness lemmas below are
trusted (and Lean's kernel).  The encoding here is hand-wired; the generic
`HomogeneousCSP` encoder that produces it is the next milestone (M3/M5).
-/

/-! ### The order encoding (`Array Constr`) -/

/-- All 9 threshold literals, positive (`Σ tⱼ`). -/
def thrPos : List (Nat × Literal) := (List.range 9).map (fun i => (1, .pos i))

/-- All 9 threshold literals, negated (`Σ ¬tⱼ`). -/
def thrNeg : List (Nat × Literal) := (List.range 9).map (fun i => (1, .neg i))

/-- The two monotonicity clauses `t^{j+1} + ¬t^j ≥ 1` for the variable whose
    thresholds start at index `b`. -/
def mono (b : Nat) : List Constr :=
  [⟨[(1, .pos (b + 1)), (1, .neg b)], 1⟩, ⟨[(1, .pos (b + 2)), (1, .neg (b + 1))], 1⟩]

/-- The full PB encoding: 6 monotonicity clauses + the two linear constraints. -/
def demoEncoding : Array Constr :=
  (mono 0 ++ mono 3 ++ mono 6 ++ [Constr.mk thrPos 7, Constr.mk thrNeg 5]).toArray

/-! ### OPB serializer (untrusted; produced the `.opb` fed to RoundingSat)

`#eval IO.print (toOPBString demoEncoding 9)` (serializer now in `Serialize.lean`,
namespace `CSP.L2S.PB`) emitted the `.opb` that RoundingSat and veripb turned into
`kernelProof` below.  It is outside the trust base. -/

/-! ### The verified PB certificate

The kernel proof emitted by `veripb --elaborate` for `demoEncoding`'s `.opb`.
PBLean's reflection checker validates it; `checkProof_sound` then yields
`formulaUnsat`.  `native_decide` runs the checker (this is the only place the
Lean compiler enters the trust base — same shape as `bv_decide`). -/
def kernelProof : String :=
"pseudo-Boolean proof version 3.0
f 8;
rup >= 0 : ~ ;
pol 9 7 1000000000000000 * + 8 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 10;
end pseudo-Boolean proof;
"

/-- The encoding is unsatisfiable — established by the external PB certificate,
    kernel-checked through PBLean's verified reflection checker. -/
theorem demo_formulaUnsat : VeriPB.Reflect.formulaUnsat demoEncoding :=
  VeriPB.Reflect.checkProof_sound demoEncoding 9 kernelProof (by native_decide)

/-! ### Order-encoding soundness (this is the trusted, hand-proved part)

A candidate solution `(x,y,z)` induces the threshold valuation `t_v^j = (v ≤ j)`,
which satisfies every constraint of `demoEncoding`.  Proved by `decide` over the
finite `Fin 4³` — non-vacuously: `le_sat`/`ge_sat` genuinely hold on the cases
where their hypotheses do. -/

/-- The threshold valuation induced by a candidate solution. -/
def demoVal (x y z : Fin 4) : Valuation := fun k =>
  if k < 3 then decide (x.val ≤ k)
  else if k < 6 then decide (y.val ≤ k - 3)
  else decide (z.val ≤ k - 6)

/-- The threshold-monotonicity clauses hold under the induced valuation. -/
theorem mono_sat (x y z : Fin 4) :
    ∀ c ∈ (mono 0 ++ mono 3 ++ mono 6 : List Constr), c.sat (demoVal x y z) := by
  simp only [Constr.sat]; revert x y z; decide

/-- The encoded `x + y + z ≤ 2` clause holds whenever the integer inequality does. -/
theorem le_sat (x y z : Fin 4) (h : x.val + y.val + z.val ≤ 2) :
    (Constr.mk thrPos 7).sat (demoVal x y z) := by
  simp only [Constr.sat]; revert x y z; decide

/-- The encoded `x + y + z ≥ 5` clause holds whenever the integer inequality does. -/
theorem ge_sat (x y z : Fin 4) (h : x.val + y.val + z.val ≥ 5) :
    (Constr.mk thrNeg 5).sat (demoVal x y z) := by
  simp only [Constr.sat]; revert x y z; decide

/-! ### The bridge: `formulaUnsat` ⟹ no integer solution -/

/-- **The demo theorem.** There is no `(x,y,z) ∈ {0,1,2,3}³` with `x+y+z ≤ 2`
    and `x+y+z ≥ 5` — proved through the full verified PB pipeline: the external
    certificate gives `formulaUnsat demoEncoding`, and the order-encoding
    soundness lemmas turn any hypothetical solution into a PB model, a
    contradiction. -/
theorem demo_unsat :
    ¬ ∃ x y z : Fin 4, x.val + y.val + z.val ≤ 2 ∧ x.val + y.val + z.val ≥ 5 := by
  rintro ⟨x, y, z, hle, hge⟩
  obtain ⟨c, hc, hnc⟩ := demo_formulaUnsat (demoVal x y z)
  apply hnc
  have hlist : demoEncoding.toList
      = mono 0 ++ mono 3 ++ mono 6 ++ [Constr.mk thrPos 7, Constr.mk thrNeg 5] := by
    simp only [demoEncoding, List.toList_toArray]
  rw [hlist] at hc
  rcases List.mem_append.1 hc with hm | hc2
  · exact mono_sat x y z c hm
  · rcases List.mem_cons.1 hc2 with rfl | hc3
    · exact le_sat x y z hle
    · rcases List.mem_cons.1 hc3 with rfl | hc4
      · exact ge_sat x y z hge
      · simp at hc4

end CSP.L2S.PB.Demo
