import CSP.L2S.Backends.PB.Encode
import CSP.L2S.Backends.PB.ToNat

namespace CSP.L2S.PB

open CSPSig
open scoped BigOperators

/-!
# PB backend — the `extend` valuation and the generic soundness spine

Bridges `formulaUnsat → ¬ ∃ solution` generically over an arbitrary `CSPSig`:

* `extend a bA auxA` builds a `Valuation S` from a CSP solution — `a`
  order-encoded into the thresholds, plus the Boolean and auxiliary settings.
  Only the threshold bits read `a`;
* `extend_orderConsistent` / `extend_sat_monotonicity` — the extended valuation
  is order-consistent and models the staircase clauses;
* `extend_intValue` — the order encoding is a faithful inverse of `intValue`;
* `csp_unsat_generic` — the aux-aware spine: PB constraints, a solution
  predicate `P` and an aux-setter `auxOf` plus a `formulaUnsat` certificate rule
  out every solution.  The gateway for aux-using encodings (Big-M `≠`, Tseitin),
  whose fresh variables must be set from the solution;
* `csp_unsat_of_linear` — the aux-free (`auxA := false`) specialization.
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

/-- The valuation induced by a CSP solution: `a` order-encoded into the
    thresholds (`thr i j` set iff `a i ≤ valuesᵢ[j]`), with `bA` and `auxA`
    passed through verbatim to the Boolean and auxiliary variables. -/
def extend (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool) (auxA : Fin S.nAux → Bool) :
    Valuation S
  | .bool b  => bA b
  | .thr i j => decide (a i ≤ S.nth i j.val)
  | .aux k   => auxA k

/-- Unfolding lemma: the threshold bit `thr i j` of `extend a bA auxA`
    is set iff `a i ≤ valuesᵢ[j]`. -/
@[simp] theorem extend_thr (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (i : Fin S.nInt) (j : Fin (S.width i)) :
    extend a bA auxA (.thr i j) = decide (a i ≤ S.nth i j.val) := rfl

/-- Unfolding lemma: the Boolean bit `bool b` of `extend a bA auxA` is `bA b`. -/
@[simp] theorem extend_bool (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (b : Fin S.nBool) :
    extend a bA auxA (.bool b) = bA b := rfl

/-- Unfolding lemma: the auxiliary bit `aux k` of `extend a bA auxA` is `auxA k`. -/
@[simp] theorem extend_aux (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (k : Fin S.nAux) :
    extend a bA auxA (.aux k) = auxA k := rfl

/-- The extended valuation is order-consistent: a satisfied threshold forces the
    next one, since the domain values increase. -/
theorem extend_orderConsistent (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) : (extend a bA auxA).orderConsistent := by
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
theorem extend_sat_monotonicity (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) :
    ∀ c ∈ S.monotonicity, c.sat (extend a bA auxA) := by
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
    show (1 : Nat) ≤ evalSum (extend a bA auxA)
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
theorem extend_intValue (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (i : Fin S.nInt) : (extend a bA auxA).intValue i = a i := by
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
      (if extend a bA auxA (.thr i j) then (1:ℤ) else 0) = (if m ≤ j.val then (1:ℤ) else 0) := by
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

/-! ### The aux-aware generic soundness spine -/

/-- **Generic UNSAT spine.** If every in-domain solution's induced valuation
    `extend a bA (auxOf a bA)` models the encoder's constraints `userConstrs`, and
    those together with the staircase clauses are `formulaUnsat`, then no solution
    exists.  The spine discharges monotonicity itself and bridges to PBLean; a
    caller proves only its own constraints.  Unlike `csp_unsat_of_linear` the
    aux/bool variables are not pinned to `false`, so aux-using encodings can set
    their fresh variables from the solution. -/
theorem csp_unsat_generic (S : CSPSig)
    (userConstrs : List (PBConstr (PBVar S)))
    (P : (Fin S.nInt → Int) → (Fin S.nBool → Bool) → Prop)
    (auxOf : (Fin S.nInt → Int) → (Fin S.nBool → Bool) → (Fin S.nAux → Bool))
    (hsound : ∀ (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool),
        (∀ i, a i ∈ S.values i) → P a bA →
        ∀ c ∈ userConstrs, c.sat (extend a bA (auxOf a bA)))
    (hunsat : VeriPB.Reflect.formulaUnsat
      ((S.monotonicity ++ userConstrs).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool),
        (∀ i, a i ∈ S.values i) ∧ P a bA := by
  rintro ⟨a, bA, hdom, hP⟩
  obtain ⟨c, hc, hnc⟩ :=
    unsat_bridge (S.monotonicity ++ userConstrs).toArray hunsat (extend a bA (auxOf a bA))
  apply hnc
  rw [List.toList_toArray, List.mem_append] at hc
  rcases hc with hmono | huser
  · exact extend_sat_monotonicity a bA (auxOf a bA) c hmono
  · exact hsound a bA hdom hP c huser

/-! ### The linear-`≤` fragment (aux-free specialization of `csp_unsat_generic`) -/

/-- The PB constraint list for a `CSPSig` and a list of linear `≤` constraints
    (`(terms, b)` means `Σ p.1·x_{p.2} ≤ b`): the order-encoding staircase
    clauses, plus each normalized linear constraint (tautologies dropped). -/
def encodeLinear (S : CSPSig) (lin : List (List (Int × Fin S.nInt) × Int)) :
    List (PBConstr (PBVar S)) :=
  S.monotonicity ++ lin.filterMap (fun c => normalize (encodeLinearLe c.1 c.2))

/-- A normalized `encodeLinearLe` constraint is modelled by `extend a bA auxA` —
    for *any* Boolean / aux setting, since the constraint mentions only
    thresholds — whenever the linear inequality holds on `a`.  The reusable
    per-constraint soundness fact for the linear fragment. -/
theorem extend_sat_encodeLinearLe (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (terms : List (Int × Fin S.nInt)) (b : Int) (c' : PBConstr (PBVar S))
    (hnorm : normalize (encodeLinearLe terms b) = some c')
    (hle : (terms.map (fun p => p.1 * a p.2)).sum ≤ b) :
    c'.sat (extend a bA auxA) := by
  rw [← normalize_sat_iff _ _ hnorm]
  apply encodeLinearLe_sound
  rw [show (terms.map (fun p => p.1 * (extend a bA auxA).intValue p.2))
        = terms.map (fun p => p.1 * a p.2) from
      List.map_congr_left (fun p _ => by rw [extend_intValue a bA auxA hdom p.2])]
  exact hle

/-- **Generic UNSAT bridge (linear fragment).** If the order encoding together
    with a list of linear `≤` constraints is `formulaUnsat`, no in-domain integer
    assignment satisfies them all.  The aux-free specialization of
    `csp_unsat_generic`. -/
theorem csp_unsat_of_linear (S : CSPSig) (lin : List (List (Int × Fin S.nInt) × Int))
    (hunsat : VeriPB.Reflect.formulaUnsat
      ((encodeLinear S lin).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ a : Fin S.nInt → Int, (∀ i, a i ∈ S.values i) ∧
        ∀ c ∈ lin, ((c.1).map (fun p => p.1 * a p.2)).sum ≤ c.2 := by
  have key : ¬ ∃ (a : Fin S.nInt → Int) (_ : Fin S.nBool → Bool),
      (∀ i, a i ∈ S.values i) ∧ ∀ c ∈ lin, ((c.1).map (fun p => p.1 * a p.2)).sum ≤ c.2 := by
    apply csp_unsat_generic S
      (lin.filterMap (fun c => normalize (encodeLinearLe c.1 c.2)))
      (fun a _ => ∀ c ∈ lin, ((c.1).map (fun p => p.1 * a p.2)).sum ≤ c.2)
      (fun _ _ _ => false)
    · intro a' bA hdom' hlin' c hc
      rw [List.mem_filterMap] at hc
      obtain ⟨lc, hlc_mem, hnorm⟩ := hc
      exact extend_sat_encodeLinearLe a' bA _ hdom' lc.1 lc.2 c hnorm (hlin' lc hlc_mem)
    · unfold encodeLinear at hunsat; exact hunsat
  rintro ⟨a, hdom, hlin⟩
  exact key ⟨a, fun _ => false, hdom, hlin⟩

end CSP.L2S.PB
