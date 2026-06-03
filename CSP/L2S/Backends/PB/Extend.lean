import CSP.L2S.Backends.PB.Encode
import CSP.L2S.Backends.PB.ToNat

namespace CSP.L2S.PB

open CSPSig
open scoped BigOperators

/-!
# PB backend — the `extend` valuation and the generic soundness spine (PLAN.md §7)

`Demo.lean` proves `formulaUnsat → ¬ ∃ solution` for one hand-wired 3-variable
instance.  This file makes that bridge **generic** over an arbitrary `CSPSig`
and a list of linear `≤` constraints:

* `extend a` order-encodes an integer assignment `a` into a `Valuation S`
  (`thr i j ↦ a i ≤ valuesᵢ[j]`);
* `extend_orderConsistent` / `extend_sat_monotonicity` — the extended valuation
  is order-consistent and models the staircase clauses (the converse direction
  of `orderConsistent_of_monotonicity`);
* `extend_intValue` — the order encoding is a faithful inverse of `intValue`:
  the recovered value of `i` is exactly `a i`;
* `csp_unsat_of_linear` — composes the above with `encodeLinearLe_sound`,
  `normalize_sat_iff`, and `unsat_bridge` into the generic UNSAT theorem.
-/

variable {S : CSPSig}

/-- `nth` is strictly monotone on in-range indices (the domain is strictly
    sorted). -/
theorem nth_lt_nth (i : Fin S.nInt) {p q : Nat} (hq : q < (S.values i).length)
    (hpq : p < q) : S.nth i p < S.nth i q := by
  have hp : p < (S.values i).length := lt_trans hpq hq
  show (S.values i).getD p 0 < (S.values i).getD q 0
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  exact (List.pairwise_iff_getElem.mp (S.sorted i)) p q hp hq hpq

/-- The order-encoding valuation induced by an integer assignment `a`:
    threshold `thr i j` is set iff `a i ≤ valuesᵢ[j]`. -/
def extend (a : Fin S.nInt → Int) : Valuation S
  | .bool _  => false
  | .thr i j => decide (a i ≤ S.nth i j.val)
  | .aux _   => false

/-- Unfolding lemma: the threshold bit `thr i j` of `extend a` is set iff `a i ≤ valuesᵢ[j]`. -/
@[simp] theorem extend_thr (a : Fin S.nInt → Int) (i : Fin S.nInt) (j : Fin (S.width i)) :
    extend a (.thr i j) = decide (a i ≤ S.nth i j.val) := rfl

/-- The extended valuation is order-consistent: a satisfied threshold forces the
    next one, since the domain values increase. -/
theorem extend_orderConsistent (a : Fin S.nInt → Int) : (extend a).orderConsistent := by
  intro i j j' hj' hj
  simp only [extend_thr, decide_eq_true_eq] at hj ⊢
  have hq : j'.val < (S.values i).length := by
    have : S.width i = (S.values i).length - 1 := rfl
    have := j'.isLt; omega
  have hmono : S.nth i j.val ≤ S.nth i j'.val :=
    le_of_lt (nth_lt_nth i hq (by omega))
  exact le_trans hj hmono

/-- The extended valuation models every staircase (monotonicity) clause — the
    converse direction of `orderConsistent_of_monotonicity`. -/
theorem extend_sat_monotonicity (a : Fin S.nInt → Int) :
    ∀ c ∈ S.monotonicity, c.sat (extend a) := by
  intro c hc
  unfold CSPSig.monotonicity at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨i, _, hc⟩ := hc
  rw [List.mem_filterMap] at hc
  obtain ⟨j, _, hc⟩ := hc
  by_cases h : j.val + 1 < S.width i
  · rw [dif_pos h, Option.some.injEq] at hc
    subst hc
    -- Clause: `t_{i,j+1} + ¬t_{i,j} ≥ 1`.
    show (1 : Nat) ≤ evalSum (extend a)
      [(1, .pos (.thr i ⟨j.val + 1, h⟩)), (1, .neg (.thr i j))]
    simp only [evalSum, evalLit, extend_thr, Nat.add_zero, Nat.one_mul]
    by_cases hj : a i ≤ S.nth i j.val
    · have hq : (j.val + 1) < (S.values i).length := by
        have : S.width i = (S.values i).length - 1 := rfl
        omega
      have : a i ≤ S.nth i (j.val + 1) := le_trans hj (le_of_lt (nth_lt_nth i hq (by omega)))
      simp [hj, this]
    · simp [hj]
  · rw [dif_neg h] at hc
    simp at hc

/-- **Faithful inverse.** The value recovered from the order encoding of `a` is
    exactly `a i` (when `a i` lies in the declared domain). -/
theorem extend_intValue (a : Fin S.nInt → Int) (hdom : ∀ i, a i ∈ S.values i)
    (i : Fin S.nInt) : (extend a).intValue i = a i := by
  -- `m` = the index of `a i` in the (strictly sorted) domain.
  obtain ⟨m, hm_len, hm_eq⟩ := List.getElem_of_mem (hdom i)
  have hai : a i = S.nth i m := by
    show a i = (S.values i).getD m 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm_len]
    exact hm_eq.symm
  have hmw : m ≤ S.width i := by
    have hw : S.width i = (S.values i).length - 1 := rfl
    omega
  -- Each threshold bit is the indicator `m ≤ j`.
  have hbit : ∀ j : Fin (S.width i),
      (if extend a (.thr i j) then (1:ℤ) else 0) = (if m ≤ j.val then (1:ℤ) else 0) := by
    intro j
    have hjlen : j.val < (S.values i).length := by
      have hw : S.width i = (S.values i).length - 1 := rfl
      have := j.isLt; omega
    have hiff : (a i ≤ S.nth i j.val) ↔ (m ≤ j.val) := by
      rw [hai]
      constructor
      · intro hle
        by_contra hmj
        rw [not_le] at hmj
        exact absurd hle (not_le.mpr (nth_lt_nth i hm_len hmj))
      · intro hmj
        rcases eq_or_lt_of_le hmj with he | hlt
        · rw [he]
        · exact le_of_lt (nth_lt_nth i hjlen hlt)
    simp only [extend_thr, decide_eq_true_eq]
    by_cases hmj : m ≤ j.val
    · rw [if_pos (hiff.mpr hmj), if_pos hmj]
    · rw [if_neg (fun hh => hmj (hiff.mp hh)), if_neg hmj]
  -- Telescope the gap-weighted sum.
  have htel : (∑ j : Fin (S.width i), S.gap i j * (if m ≤ j.val then (1:ℤ) else 0))
      = S.nth i (S.width i) - S.nth i m := by
    have hreindex : (∑ j : Fin (S.width i), S.gap i j * (if m ≤ j.val then (1:ℤ) else 0))
        = ∑ k ∈ Finset.range (S.width i),
            (S.nth i (k + 1) - S.nth i k) * (if m ≤ k then (1:ℤ) else 0) := by
      rw [← Fin.sum_univ_eq_sum_range]
      rfl
    rw [hreindex]
    have hind : ∀ k ∈ Finset.range (S.width i),
        (S.nth i (k + 1) - S.nth i k) * (if m ≤ k then (1:ℤ) else 0)
          = if m ≤ k then (S.nth i (k + 1) - S.nth i k) else 0 := by
      intro k _; by_cases hmk : m ≤ k <;> simp [hmk]
    rw [Finset.sum_congr rfl hind, ← Finset.sum_filter]
    have hfilter :
        (Finset.range (S.width i)).filter (fun k => m ≤ k) = Finset.Ico m (S.width i) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hfilter, Finset.sum_Ico_eq_sub _ hmw, Finset.sum_range_sub, Finset.sum_range_sub]
    ring
  unfold Valuation.intValue
  simp only [hbit]
  rw [htel, show S.maxVal i = S.nth i (S.width i) from rfl, hai]
  ring

/-! ### The generic soundness theorem -/

/-- The PB constraint list for a `CSPSig` and a list of linear `≤` constraints
    (`(terms, b)` means `Σ p.1·x_{p.2} ≤ b`): the order-encoding staircase
    clauses, plus each normalized linear constraint (tautologies dropped). -/
def encodeLinear (S : CSPSig) (lin : List (List (Int × Fin S.nInt) × Int)) :
    List (PBConstr (PBVar S)) :=
  S.monotonicity ++ lin.filterMap (fun c => normalize (encodeLinearLe c.1 c.2))

/-- **Generic UNSAT bridge.** If the order encoding of a `CSPSig` together with a
    list of linear `≤` constraints is `formulaUnsat` (kernel-checked through
    PBLean), then no in-domain integer assignment satisfies all the linear
    constraints.  Generalizes `Demo.demo_unsat` to an arbitrary signature. -/
theorem csp_unsat_of_linear (S : CSPSig) (lin : List (List (Int × Fin S.nInt) × Int))
    (hunsat : VeriPB.Reflect.formulaUnsat
      ((encodeLinear S lin).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ a : Fin S.nInt → Int, (∀ i, a i ∈ S.values i) ∧
        ∀ c ∈ lin, ((c.1).map (fun p => p.1 * a p.2)).sum ≤ c.2 := by
  rintro ⟨a, hdom, hlin⟩
  obtain ⟨c, hc, hnc⟩ := unsat_bridge (encodeLinear S lin).toArray hunsat (extend a)
  apply hnc
  rw [List.toList_toArray] at hc
  unfold encodeLinear at hc
  rw [List.mem_append] at hc
  rcases hc with hmono | hlinmem
  · exact extend_sat_monotonicity a c hmono
  · rw [List.mem_filterMap] at hlinmem
    obtain ⟨lc, hlc_mem, hnorm⟩ := hlinmem
    rw [← normalize_sat_iff _ _ hnorm (extend a)]
    apply encodeLinearLe_sound
    have hval := hlin lc hlc_mem
    have hmap : (lc.1.map (fun p => p.1 * (extend a).intValue p.2))
        = lc.1.map (fun p => p.1 * a p.2) :=
      List.map_congr_left (fun p _ => by rw [extend_intValue a hdom p.2])
    rw [hmap]; exact hval

end CSP.L2S.PB
