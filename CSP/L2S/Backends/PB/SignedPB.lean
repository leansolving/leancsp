import CSP.L2S.Backends.PB.PBConstr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace CSP.L2S.PB

/-!
# PB backend — signed constraints and their normalization

The per-constraint encoders produce **signed** linear constraints
`Σ aᵢ·⟦ℓᵢ⟧ ≥ rhs`, while the kernel constraints (`PBConstr`) use non-negative
coefficients and a `Nat` degree.  `normalize` bridges the two via the identity
`a·⟦ℓ⟧ = |a|·⟦¬ℓ⟧ + a` for `a < 0`, returning `none` for a tautology.

Like-term merging and complementary-pair cancellation are intentionally not
performed: they are not needed for soundness. -/

variable {V : Type}

/-- Encoder-level PB constraint with **signed** coefficients (intermediate form).
    Semantics: `Σ (a, ℓ) ∈ terms, a · ⟦ℓ⟧ ≥ rhs`. -/
structure SignedPBConstr (V : Type) where
  /-- Signed weighted literal terms. -/
  terms : List (Int × Lit V)
  /-- The (signed) right-hand side. -/
  rhs   : Int

/-- The signed weighted sum `Σ a · ⟦ℓ⟧` (over `ℤ`). -/
def signedEval (v : V → Bool) (ts : List (Int × Lit V)) : Int :=
  (ts.map (fun p => p.1 * (evalLit v p.2 : Int))).sum

/-- A signed constraint is satisfied when its signed sum meets the rhs. -/
def SignedPBConstr.sat (v : V → Bool) (c : SignedPBConstr V) : Prop :=
  signedEval v c.terms ≥ c.rhs

/-- Normalize one signed term to non-negative coefficient form: a positive
    coefficient is kept, a negative `a·ℓ` becomes `|a|·¬ℓ`, a zero is dropped. -/
def normLit (a : Int) (ℓ : Lit V) : List (Term V) :=
  if a > 0 then [(a.toNat, ℓ)] else if a < 0 then [((-a).toNat, ℓ.negate)] else []

/-- The degree shift contributed by one term: `|a|` for negative `a`, else `0`
    (the constant `a` produced when rewriting `a·ℓ = |a|·¬ℓ + a`). -/
def normShift (a : Int) : Int := if a < 0 then -a else 0

/-- **Per-term identity**: `a·⟦ℓ⟧ = (value of normLit) − normShift`. -/
theorem signed_term (v : V → Bool) (a : Int) (ℓ : Lit V) :
    a * (evalLit v ℓ : Int) = (evalSum v (normLit a ℓ) : Int) - normShift a := by
  have hneg : (evalLit v ℓ.negate : Int) = 1 - (evalLit v ℓ : Int) := by
    have := evalLit_negate_add v ℓ; omega
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have h1 : ¬ a > 0 := by omega
    have hna : (0 : Int) ≤ -a := by omega
    simp only [normLit, normShift, if_neg h1, if_pos ha, evalSum, Nat.add_zero, Nat.cast_mul]
    rw [Int.toNat_of_nonneg hna, hneg]
    ring
  · subst ha
    simp [normLit, normShift, evalSum]
  · have h2 : ¬ a < 0 := by omega
    have hpa : (0 : Int) ≤ a := by omega
    simp only [normLit, normShift, if_pos ha, if_neg h2, evalSum, Nat.add_zero, Nat.cast_mul]
    rw [Int.toNat_of_nonneg hpa]
    ring

/-- **List identity**: the signed sum equals the normalized (natural) sum minus
    the accumulated degree shift. -/
theorem signed_eq (v : V → Bool) (ts : List (Int × Lit V)) :
    signedEval v ts
      = (evalSum v (ts.flatMap (fun p => normLit p.1 p.2)) : Int)
        - (ts.map (fun p => normShift p.1)).sum := by
  induction ts with
  | nil => simp [signedEval, evalSum]
  | cons hd tl ih =>
    obtain ⟨a, ℓ⟩ := hd
    have ht := signed_term v a ℓ
    simp only [signedEval, List.map_cons, List.sum_cons, List.flatMap_cons, evalSum_append,
      Nat.cast_add] at ih ⊢
    linarith [ht, ih]

/-- Normalize a signed constraint to natural-coefficient form, or `none` if it is
    a tautology (`degree ≤ 0`, always satisfied since the natural sum is `≥ 0`). -/
def normalize (c : SignedPBConstr V) : Option (PBConstr V) :=
  let deg := c.rhs + (c.terms.map (fun p => normShift p.1)).sum
  if deg ≤ 0 then none
  else some ⟨c.terms.flatMap (fun p => normLit p.1 p.2), deg.toNat⟩

/-- Normalization preserves satisfaction when it produces a constraint. -/
theorem normalize_sat_iff (c : SignedPBConstr V) (c' : PBConstr V)
    (h : normalize c = some c') (v : V → Bool) :
    c.sat v ↔ c'.sat v := by
  have hkey := signed_eq v c.terms
  simp only [normalize] at h
  split at h
  · simp at h
  · rename_i hpos
    rw [Option.some.injEq] at h
    subst h
    simp only [SignedPBConstr.sat, PBConstr.sat, hkey]
    omega

/-- A `none` normalization means the constraint is a tautology. -/
theorem normalize_none_tautology (c : SignedPBConstr V)
    (h : normalize c = none) (v : V → Bool) :
    c.sat v := by
  have hkey := signed_eq v c.terms
  simp only [normalize] at h
  split at h
  · rename_i hle
    simp only [SignedPBConstr.sat, hkey]
    omega
  · simp at h

end CSP.L2S.PB
