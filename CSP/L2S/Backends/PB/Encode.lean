/-
PB backend — the linear-`≤` encoder (PLAN.md §6.2).

`encodeLinearLe terms b` turns a linear arithmetic constraint `Σ aᵢ·xᵢ ≤ b` over
CSP integer variables into a single **signed** PB constraint over the threshold
variables, with gap-weighted coefficients.  Soundness (`encodeLinearLe_sound`)
is exactly the forward direction of the substitution theorem (M2,
`linear_le_of_threshold_sum`): the heavy lifting is bridging the encoder's
`flatMap`/`finRange` term list to the theorem's `Finset`-over-`Fin` sums.
-/
import CSP.L2S.Backends.PB.SignedPB
import CSP.L2S.Backends.PB.Substitution

namespace CSP.L2S.PB

open scoped BigOperators

variable {V : Type} {S : CSPSig}

/-- `signedEval` distributes over list append. -/
theorem signedEval_append (v : V → Bool) (a b : List (Int × Lit V)) :
    signedEval v (a ++ b) = signedEval v a + signedEval v b := by
  simp [signedEval, List.sum_append]

/-- `signedEval` of a `flatMap` is the sum of the pieces' `signedEval`s. -/
theorem signedEval_flatMap {α : Type} (v : V → Bool) (l : List α)
    (g : α → List (Int × Lit V)) :
    signedEval v (l.flatMap g) = (l.map (fun x => signedEval v (g x))).sum := by
  induction l with
  | nil => simp [signedEval]
  | cons hd tl ih =>
    rw [List.flatMap_cons, signedEval_append, ih, List.map_cons, List.sum_cons]

/-- The per-variable inner identity: the `finRange`-indexed threshold term list
    evaluates to the `Fin`-sum used by the substitution theorem. -/
theorem signedEval_inner (v : Valuation S) (a : Int) (i : Fin S.nInt) :
    signedEval v ((List.finRange (S.width i)).map
        (fun j => (a * S.gap i j, Lit.pos (PBVar.thr i j))))
      = a * ∑ j : Fin (S.width i), S.gap i j * (if v (PBVar.thr i j) then (1 : ℤ) else 0) := by
  unfold signedEval
  rw [List.map_map, ← List.ofFn_eq_map, List.sum_ofFn, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [Function.comp_apply, evalLit]
  split <;> push_cast <;> ring

/-- Encode `Σ aᵢ·xᵢ ≤ b` (the `terms` list pairs each coefficient with a
    variable index) as a signed PB constraint over the threshold variables:
    `Σᵢ aᵢ·(Σⱼ gapᵢⱼ·tᵢⱼ) ≥ (Σᵢ aᵢ·maxVal i) − b`. -/
def encodeLinearLe (terms : List (Int × Fin S.nInt)) (b : Int) : SignedPBConstr (PBVar S) where
  terms := terms.flatMap (fun p =>
    (List.finRange (S.width p.2)).map (fun j => (p.1 * S.gap p.2 j, Lit.pos (PBVar.thr p.2 j))))
  rhs := (terms.map (fun p => p.1 * S.maxVal p.2)).sum - b

/-- The signed sum of the encoding equals the substitution theorem's
    threshold-sum side. -/
theorem signedEval_encode (v : Valuation S) (terms : List (Int × Fin S.nInt)) (b : Int) :
    signedEval v (encodeLinearLe terms b).terms
      = (terms.map (fun p => p.1 *
          ∑ j : Fin (S.width p.2), S.gap p.2 j * (if v (.thr p.2 j) then (1 : ℤ) else 0))).sum := by
  show signedEval v (terms.flatMap _) = _
  rw [signedEval_flatMap]
  refine congrArg List.sum (List.map_congr_left (fun p _ => ?_))
  exact signedEval_inner v p.1 p.2

/-- **Soundness.** If the linear constraint `Σ aᵢ·xᵢ ≤ b` holds under the value
    recovered from `v`, then the encoded PB constraint is satisfied by `v`.
    Immediate from the substitution theorem. -/
theorem encodeLinearLe_sound (v : Valuation S) (terms : List (Int × Fin S.nInt)) (b : Int)
    (h : (terms.map (fun p => p.1 * v.intValue p.2)).sum ≤ b) :
    (encodeLinearLe terms b).sat v := by
  have hsub := (linear_le_of_threshold_sum v terms b).mp h
  show signedEval v (encodeLinearLe terms b).terms ≥ (encodeLinearLe terms b).rhs
  rw [signedEval_encode]
  exact hsub

end CSP.L2S.PB
