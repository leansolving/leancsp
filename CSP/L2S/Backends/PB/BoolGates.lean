import CSP.L2S.Backends.PB.SignedPB

namespace CSP.L2S.PB

/-!
# PB backend — Boolean primitives via Tseitin gates (PLAN §6.7)

Reification ("Tseitin") gates for the Boolean connectives `¬, ∧, ∨, →, ↔`: each
introduces an output literal `z` (typically a fresh `aux`) constrained to equal the
connective applied to the input literals, via 2–4 PB clauses.  The encoders work at
the **literal level** (over any variable type `V`), the reusable core a recursive
`BoolExpr` compiler would call on each subformula.

The gate semantics is stated on the literals' Boolean *bits* `evalLit v ℓ ∈ {0,1}`
using arithmetic on bits — `∧ = min`, `∨ = max`, `¬ = 1 − ·`, `↔ = 1 − |·−·|`
(written with `max − min` to stay in `ℕ`).  Each clause is a sum-`≥ 1` constraint,
so every per-connective soundness lemma is a uniform `simp` (unfold the clause sat
to a linear bit-sum) followed by `omega` (the bit bounds `≤ 1`, the negation
identities `ℓ + ¬ℓ = 1`, and the gate relation).

The **aux-setter** for the generic spine (`csp_unsat_generic`) sets each gate's
output aux to the connective of its inputs under the solution's Boolean part `bA`
(`extend_bool`/`extend_aux` then read the bits) — demonstrated in `BoolGatesTest`.
-/

variable {V : Type}

/-- A disjunctive clause `Σ ⟦ℓᵢ⟧ ≥ 1` (at least one literal true). -/
def clause (lits : List (Lit V)) : SignedPBConstr V :=
  { terms := lits.map (fun ℓ => ((1 : Int), ℓ)), rhs := 1 }

/-! ### The five connective gates (output literal `z`) -/

/-- `z ↔ ¬x`: clauses `z ∨ x`, `¬z ∨ ¬x`. -/
def gateNot (z x : Lit V) : List (SignedPBConstr V) :=
  [clause [z, x], clause [z.negate, x.negate]]

/-- `z ↔ (x ∧ y)`: clauses `¬z ∨ x`, `¬z ∨ y`, `z ∨ ¬x ∨ ¬y`. -/
def gateAnd (z x y : Lit V) : List (SignedPBConstr V) :=
  [clause [z.negate, x], clause [z.negate, y], clause [z, x.negate, y.negate]]

/-- `z ↔ (x ∨ y)`: clauses `z ∨ ¬x`, `z ∨ ¬y`, `¬z ∨ x ∨ y`. -/
def gateOr (z x y : Lit V) : List (SignedPBConstr V) :=
  [clause [z, x.negate], clause [z, y.negate], clause [z.negate, x, y]]

/-- `z ↔ (x → y)`, i.e. `z ↔ (¬x ∨ y)` — the `∨` gate with `x` negated. -/
def gateImp (z x y : Lit V) : List (SignedPBConstr V) :=
  gateOr z x.negate y

/-- `z ↔ (x ↔ y)`: clauses `¬z ∨ ¬x ∨ y`, `¬z ∨ x ∨ ¬y`, `z ∨ x ∨ y`, `z ∨ ¬x ∨ ¬y`. -/
def gateIff (z x y : Lit V) : List (SignedPBConstr V) :=
  [clause [z.negate, x.negate, y], clause [z.negate, x, y.negate],
   clause [z, x, y], clause [z, x.negate, y.negate]]

/-! ### Per-connective soundness

Each lemma: if `z`'s bit equals the connective of `x`/`y`'s bits, all clauses hold.
-/

/-- A satisfied clause is a bit-sum `≥ 1`; the shared reduction the gate proofs use. -/
private theorem clause_sat_eq (v : V → Bool) (lits : List (Lit V)) :
    (clause lits).sat v ↔ (1 : Int) ≤ (lits.map (fun ℓ => (evalLit v ℓ : Int))).sum := by
  simp only [clause, SignedPBConstr.sat, signedEval, List.map_map, Function.comp_def, one_mul]

/-- **`¬` soundness.** -/
theorem gateNot_sound (v : V → Bool) (z x : Lit V)
    (h : evalLit v z = 1 - evalLit v x) : ∀ c ∈ gateNot z x, c.sat v := by
  have hx := evalLit_le_one v x; have hz := evalLit_le_one v z
  have hnz := evalLit_negate_add v z; have hnx := evalLit_negate_add v x
  intro c hc
  simp only [gateNot, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;>
    · rw [clause_sat_eq]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

/-- **`∧` soundness** (`∧ = min` on bits). -/
theorem gateAnd_sound (v : V → Bool) (z x y : Lit V)
    (h : evalLit v z = min (evalLit v x) (evalLit v y)) : ∀ c ∈ gateAnd z x y, c.sat v := by
  have hx := evalLit_le_one v x; have hy := evalLit_le_one v y; have hz := evalLit_le_one v z
  have hnz := evalLit_negate_add v z; have hnx := evalLit_negate_add v x
  have hny := evalLit_negate_add v y
  intro c hc
  simp only [gateAnd, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;>
    · rw [clause_sat_eq]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

/-- **`∨` soundness** (`∨ = max` on bits). -/
theorem gateOr_sound (v : V → Bool) (z x y : Lit V)
    (h : evalLit v z = max (evalLit v x) (evalLit v y)) : ∀ c ∈ gateOr z x y, c.sat v := by
  have hx := evalLit_le_one v x; have hy := evalLit_le_one v y; have hz := evalLit_le_one v z
  have hnz := evalLit_negate_add v z; have hnx := evalLit_negate_add v x
  have hny := evalLit_negate_add v y
  intro c hc
  simp only [gateOr, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;>
    · rw [clause_sat_eq]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

/-- **`→` soundness** (`x → y` is `¬x ∨ y`, so `z = max (1 − x) y`). -/
theorem gateImp_sound (v : V → Bool) (z x y : Lit V)
    (h : evalLit v z = max (1 - evalLit v x) (evalLit v y)) : ∀ c ∈ gateImp z x y, c.sat v := by
  refine gateOr_sound v z x.negate y ?_
  rw [h]
  have hnx := evalLit_negate_add v x
  have hx := evalLit_le_one v x
  omega

/-- **`↔` soundness** (`x ↔ y` is `1 − |x − y| = 1 − (max − min)` on bits). -/
theorem gateIff_sound (v : V → Bool) (z x y : Lit V)
    (h : evalLit v z = 1 - (max (evalLit v x) (evalLit v y) - min (evalLit v x) (evalLit v y))) :
    ∀ c ∈ gateIff z x y, c.sat v := by
  have hx := evalLit_le_one v x; have hy := evalLit_le_one v y; have hz := evalLit_le_one v z
  have hnz := evalLit_negate_add v z; have hnx := evalLit_negate_add v x
  have hny := evalLit_negate_add v y
  intro c hc
  simp only [gateIff, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;>
    · rw [clause_sat_eq]; simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

/-! ### Unit test: the `∧` gate with the aux-setter pattern

A 3-variable propositional valuation; the gate output `z`'s bit is set to the AND
of the input bits (the aux-setter `auxOf z := bx && by`), so `gateAnd_sound` applies.
-/

namespace BoolGatesTest

/-- Three propositional variables (`0`/`1`/`2`), `2` the gate output. -/
abbrev Var := Fin 3

/-- A valuation with `x₀, x₁` true and the output `x₂ = (x₀ ∧ x₁) = true`. -/
def vG : Var → Bool := fun _ => true

-- The output bit equals `min` of the input bits — the aux-setter discharged the relation.
example : evalLit vG (.pos 2) = min (evalLit vG (.pos 0)) (evalLit vG (.pos 1)) := by decide

-- Hence the AND-gate clauses are all satisfied.
example : ∀ c ∈ gateAnd (Lit.pos (2 : Var)) (.pos 0) (.pos 1), c.sat vG :=
  gateAnd_sound vG (.pos 2) (.pos 0) (.pos 1) (by decide)

end BoolGatesTest

end CSP.L2S.PB
