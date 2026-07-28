import CSP.L2S.Backends.PB.Semantics

namespace CSP.L2S.PB

open scoped BigOperators

/-!
# PB backend — the substitution theorem

Under the order encoding a linear constraint `Σ aᵢ·xᵢ ≤ b` over CSP integer
variables becomes a single linear PB constraint over the threshold variables,
with gap-weighted coefficients.  Every linear encoding (`≤`, `≥`, `=`, `<`, `>`,
and `≠` via Big-M) is justified through `linear_le_of_threshold_sum`.

The identity is pure algebra; order consistency is *not* needed here (that is
what makes the recovered value land in the domain — see `intValue_mem_values`).
-/

variable {S : CSPSig}

/-- **The substitution theorem.** For a linear combination `Σ aᵢ·xᵢ` given as a
    list of `(coefficient, variable)` pairs, `Σ aᵢ·xᵢ ≤ b` is equivalent to the
    PB constraint `Σᵢ aᵢ·(Σⱼ gapᵢⱼ·⟦thr i j⟧) ≥ (Σᵢ aᵢ·maxVal i) − b`.  The
    gap-weighted coefficients generalize the interval-domain order encoding to
    arbitrary finite domains. -/
theorem linear_le_of_threshold_sum (v : Valuation S)
    (terms : List (Int × Fin S.nInt)) (b : Int) :
    (terms.map (fun p => p.1 * v.intValue p.2)).sum ≤ b
      ↔
    (terms.map (fun p => p.1 *
        ∑ j : Fin (S.width p.2), S.gap p.2 j * (if v (.thr p.2 j) then (1 : ℤ) else 0))).sum
      ≥ (terms.map (fun p => p.1 * S.maxVal p.2)).sum - b := by
  -- Distribute `intValue = maxVal − thresholdSum` across the linear combination.
  have key : (terms.map (fun p => p.1 * v.intValue p.2)).sum
      = (terms.map (fun p => p.1 * S.maxVal p.2)).sum
        - (terms.map (fun p => p.1 *
            ∑ j : Fin (S.width p.2),
              S.gap p.2 j * (if v (.thr p.2 j) then (1 : ℤ) else 0))).sum := by
    induction terms with
    | nil => simp
    | cons p rest ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      have hp : p.1 * v.intValue p.2
          = p.1 * S.maxVal p.2
            - p.1 * ∑ j : Fin (S.width p.2),
                S.gap p.2 j * (if v (.thr p.2 j) then (1 : ℤ) else 0) := by
        unfold Valuation.intValue; ring
      rw [hp]; ring
  rw [key]; omega

/-! ### Sanity check: two variables over `{0, 2, 4}`. -/

namespace DemoTest

/-- Two integer variables, each with the sparse domain `{0, 2, 4}`
    (gaps `2, 2`, so the order encoding has nontrivial gap coefficients). -/
def demoSig : CSPSig where
  nInt := 2
  nBool := 0
  nAux := 0
  values := fun _ => [0, 2, 4]
  sorted := by intro _; decide
  nonempty := by intro _; decide

/-- A valuation with variable `0`'s "`≤ 2`" threshold set (so `x₀ = 2`) and no
    threshold set for variable `1` (so `x₁ = 4`). -/
def demoVal : Valuation demoSig := fun x =>
  match x with
  | .thr i j => decide (i.val = 0 ∧ j.val = 1)
  | _ => false

-- `intValue` recovers the intended domain values through the gap-weighted sum.
example : demoVal.intValue (0 : Fin 2) = 2 := by decide
example : demoVal.intValue (1 : Fin 2) = 4 := by decide

-- Hence `x₀ + x₁ = 6` violates the linear constraint `x₀ + x₁ ≤ 4`.
example :
    ¬ (([(1, (0 : Fin 2)), (1, 1)].map fun p => p.1 * demoVal.intValue p.2).sum ≤ 4) := by
  decide

end DemoTest

end CSP.L2S.PB
