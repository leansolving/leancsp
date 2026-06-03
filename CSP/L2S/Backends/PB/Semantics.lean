import CSP.L2S.Backends.PB.PBVar
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

namespace CSP.L2S.PB

open CSPSig
open scoped BigOperators

/-!
# PB backend — semantics of the order encoding

Recovers the integer value of each CSP variable from a Boolean valuation of the
threshold variables (`intValue`), states the monotonicity ("staircase")
constraints that make the threshold bits order-consistent, and proves the
foundational lemma that an order-consistent valuation always recovers a value
inside the declared finite domain (`intValue_mem_values`).
-/

variable {S : CSPSig}

/-- A valuation of the PB variables of signature `S`. -/
abbrev Valuation (S : CSPSig) := PBVar S → Bool

namespace Valuation

/-- The integer value recovered for variable `i` under valuation `v`:
    `maxVal i − Σⱼ gapⱼ · ⟦thr i j⟧`.  Under order consistency the true
    thresholds form an up-set, the gap-weighted sum telescopes, and this lands
    on a declared domain value (`intValue_mem_values`). -/
def intValue (v : Valuation S) (i : Fin S.nInt) : Int :=
  S.maxVal i - ∑ j : Fin (S.width i), S.gap i j * (if v (.thr i j) then 1 else 0)

/-- Order consistency (adjacency form): along each integer variable, a true
    threshold forces the next threshold true (`thr i j` ⇒ `thr i (j+1)`).
    Equivalent to satisfying `S.monotonicity` — see
    `orderConsistent_of_monotonicity`. -/
def orderConsistent (v : Valuation S) : Prop :=
  ∀ (i : Fin S.nInt) (j j' : Fin (S.width i)),
    j'.val = j.val + 1 → v (.thr i j) = true → v (.thr i j') = true

end Valuation

/-- Monotonicity (staircase) constraints: for each integer variable `i` and each
    adjacent threshold pair `(j, j+1)`, the clause `t_{i,j+1} + ¬t_{i,j} ≥ 1`,
    i.e. `t_{i,j} → t_{i,j+1}`. -/
def CSPSig.monotonicity (S : CSPSig) : List (PBConstr (PBVar S)) :=
  (List.finRange S.nInt).flatMap fun i =>
    (List.finRange (S.width i)).filterMap fun j =>
      if h : j.val + 1 < S.width i then
        some { terms := [(1, .pos (.thr i ⟨j.val + 1, h⟩)), (1, .neg (.thr i j))]
               degree := 1 }
      else none

/-- Satisfying every monotonicity constraint implies the semantic order
    consistency predicate. -/
theorem orderConsistent_of_monotonicity (v : Valuation S)
    (h : ∀ c ∈ S.monotonicity, c.sat v) : v.orderConsistent := by
  intro i j j' hj' hj
  -- `j' = j + 1 < width i`, so the staircase clause for `(i, j)` is emitted.
  have h2 : j.val + 1 < S.width i := hj' ▸ j'.isLt
  have hmem :
      (⟨[(1, .pos (.thr i ⟨j.val + 1, h2⟩)), (1, .neg (.thr i j))], 1⟩ : PBConstr (PBVar S))
        ∈ S.monotonicity := by
    unfold CSPSig.monotonicity
    rw [List.mem_flatMap]
    refine ⟨i, List.mem_finRange i, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨j, List.mem_finRange j, by rw [dif_pos h2]⟩
  have hsat := h _ hmem
  simp only [PBConstr.sat, evalSum, evalLit] at hsat
  -- The clause forces the next threshold true once `thr i j` is true.
  have hjj : j' = ⟨j.val + 1, h2⟩ := Fin.ext hj'
  rw [hjj]
  by_contra hbb
  rw [if_neg hbb, if_pos hj] at hsat
  omega

/-- A globally monotone (nondecreasing) Boolean sequence that is `true` at `w`
    has a switch point `m ≤ w`: `false` strictly below `m`, `true` from `m` on. -/
private theorem exists_switch (t : ℕ → Bool) (w : ℕ)
    (hmono : ∀ k, t k = true → t (k + 1) = true) (htw : t w = true) :
    ∃ m, m ≤ w ∧ (∀ k, k < m → t k = false) ∧ (∀ k, m ≤ k → t k = true) := by
  classical
  have hex : ∃ k, t k = true := ⟨w, htw⟩
  refine ⟨Nat.find hex, Nat.find_le htw, ?_, ?_⟩
  · intro k hk
    have h := Nat.find_min hex hk
    simpa using h
  · intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact Nat.find_spec hex
    | succ n _ ih => exact hmono n ih

/-- Under order consistency, the gap-weighted threshold sum telescopes: it equals
    `valuesᵢ[width] − valuesᵢ[m]` for the switch point `m ≤ width` (the index of
    the recovered domain value). -/
private theorem gap_fin_sum_eq (i : Fin S.nInt) (v : Valuation S)
    (hv : v.orderConsistent) :
    ∃ m, m ≤ S.width i ∧
      (∑ j : Fin (S.width i), S.gap i j * (if v (.thr i j) then (1 : ℤ) else 0))
        = S.nth i (S.width i) - S.nth i m := by
  classical
  -- ℕ-indexed view of the threshold bits, defaulting to `true` past the top.
  let t : ℕ → Bool := fun k => if h : k < S.width i then v (.thr i ⟨k, h⟩) else true
  have htlt : ∀ k (h : k < S.width i), t k = v (.thr i ⟨k, h⟩) := fun k h => dif_pos h
  have htge : ∀ k, ¬ (k < S.width i) → t k = true := fun k h => dif_neg h
  -- `t` is globally monotone.
  have hmono : ∀ k, t k = true → t (k + 1) = true := by
    intro k hk
    by_cases hk1 : k + 1 < S.width i
    · have hklt : k < S.width i := by omega
      rw [htlt k hklt] at hk
      rw [htlt (k + 1) hk1]
      exact hv i ⟨k, hklt⟩ ⟨k + 1, hk1⟩ rfl hk
    · rw [htge (k + 1) hk1]
  have htw : t (S.width i) = true := htge (S.width i) (lt_irrefl _)
  obtain ⟨m, hmw, hlt, hge⟩ := exists_switch t (S.width i) hmono htw
  refine ⟨m, hmw, ?_⟩
  -- Reindex the `Fin (width i)` sum to a `range (width i)` sum over ℕ.
  have hreindex :
      (∑ j : Fin (S.width i), S.gap i j * (if v (.thr i j) then (1 : ℤ) else 0))
        = ∑ k ∈ Finset.range (S.width i),
            (S.nth i (k + 1) - S.nth i k) * (if t k then (1 : ℤ) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hg : S.gap i j = S.nth i (↑j + 1) - S.nth i ↑j := rfl
    have hvj : v (.thr i j) = t ↑j := (htlt ↑j j.isLt).symm
    rw [hg, hvj]
  rw [hreindex]
  -- Replace each threshold bit by the `m`-threshold, then telescope.
  have hind : ∀ k ∈ Finset.range (S.width i),
      (S.nth i (k + 1) - S.nth i k) * (if t k then (1 : ℤ) else 0)
        = if m ≤ k then (S.nth i (k + 1) - S.nth i k) else 0 := by
    intro k _
    by_cases hmk : m ≤ k
    · rw [hge k hmk]; simp [hmk]
    · have hkm : k < m := by omega
      rw [hlt k hkm]; simp [hmk]
  rw [Finset.sum_congr rfl hind, ← Finset.sum_filter]
  have hfilter :
      (Finset.range (S.width i)).filter (fun k => m ≤ k) = Finset.Ico m (S.width i) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hfilter, Finset.sum_Ico_eq_sub _ hmw, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

namespace Valuation

/-- **Foundational lemma.** Under order consistency, the recovered integer value
    of any variable is one of its declared domain values. -/
theorem intValue_mem_values (v : Valuation S)
    (hv : v.orderConsistent) (i : Fin S.nInt) :
    v.intValue i ∈ S.values i := by
  obtain ⟨m, hmw, hsum⟩ := gap_fin_sum_eq i v hv
  have hval : v.intValue i = S.nth i m := by
    unfold Valuation.intValue
    rw [hsum, show S.maxVal i = S.nth i (S.width i) from rfl]
    ring
  have hmlt : m < (S.values i).length := by
    have hne := S.nonempty i
    have hwd : S.width i = (S.values i).length - 1 := rfl
    omega
  have hget : S.nth i m = (S.values i)[m]'hmlt := by
    show (S.values i).getD m 0 = (S.values i)[m]'hmlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmlt]
    rfl
  rw [hval, hget]
  exact List.getElem_mem hmlt

end Valuation

end CSP.L2S.PB
