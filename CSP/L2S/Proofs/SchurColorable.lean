import CSP.L2S.Proofs.SchurSB

/-!
# Schur numbers — the pure-mathematical bridge

Connects the Schur CSP (`Schur.schur_csp n c`) to the textbook statement
`SchurColorable n c`: the integers `{1,…,n}` admit a `c`-colouring with no monochromatic
`x + y = z`.  The bridge `schur_csp_iff_colorable` turns CSP-satisfiability into this
math statement, so a kernel-checked witness (`csp_sat_file`) yields a clean
`SchurColorable n c` lower bound, and a verified PB-UNSAT yields `¬ SchurColorable (n+1) c`.

Constraint satisfaction is read through `patternHolds` (i.e. `satisfiesConstraintInt`)
rather than the dynamic-constraint checker; the leaf lemmas `bound_sat_iff` and
`schur_triple_sat_iff` are stated accordingly, and the rest is independent of that choice because
`schurTriples`/`schur_csp_triples` are defined identically in both projects.
-/

open CSP.L2S

namespace Schur

/-! ### Mathematical Definition -/

/-- A `c`-colouring of `{1,…,n}` is sum-free if no monochromatic `x + y = z`.
    Uses 0-indexing: variable `i` represents integer `i+1`,
    so `x + y = z` becomes `(i+1) + (j+1) = (k+1)`, i.e. `k = i + j + 1`. -/
def SchurColorable (n c : ℕ) : Prop :=
  ∃ χ : Fin n → Fin c, ∀ (i j k : Fin n),
    ¬(k.val = i.val + j.val + 1 ∧ χ i = χ j ∧ χ j = χ k)

/-- Decidability: collapse the nested quantifiers to a single product type. -/
instance decidableSchurColorable (n c : ℕ) : Decidable (SchurColorable n c) :=
  decidable_of_iff
    (∃ χ : Fin n → Fin c, ∀ t : Fin n × Fin n × Fin n,
      ¬(t.2.2.val = t.1.val + t.2.1.val + 1 ∧ χ t.1 = χ t.2.1 ∧ χ t.2.1 = χ t.2.2))
    ⟨fun ⟨χ, h⟩ => ⟨χ, fun i j k => h ⟨i, j, k⟩⟩,
     fun ⟨χ, h⟩ => ⟨χ, fun ⟨i, j, k⟩ => h i j k⟩⟩

/-! ### Leaf lemmas (patternHolds idiom) -/

section Bridge

/-- `valAt` of a `Fin`-index coercion is just function application. -/
private lemma valAt_fin {n : ℕ} (a : IntAssignment n) (v : Fin n) :
    valAt a v.val = a v := by
  rw [valAt, dif_pos v.isLt]

/-- The smart `bound` constraint unfolds to a range check on `a v`. -/
lemma bound_sat_iff {n : ℕ} (v : Fin n) (lb ub : ℤ) (a : IntAssignment n) :
    IntCSP.satisfiesConstraintInt (bound v lb ub) a ↔ (lb ≤ a v ∧ a v ≤ ub) := by
  simp only [IntCSP.satisfiesConstraintInt, bound, patternHolds, valAt_fin]

/-- The smart `schur_triple` constraint unfolds to a not-all-equal disjunction. -/
lemma schur_triple_sat_iff {n : ℕ} (v1 v2 v3 : Fin n) (a : IntAssignment n) :
    IntCSP.satisfiesConstraintInt (schur_triple v1 v2 v3) a ↔
    (a v1 ≠ a v2 ∨ a v1 ≠ a v3 ∨ a v2 ≠ a v3) := by
  simp only [IntCSP.satisfiesConstraintInt, schur_triple, patternHolds, valAt_fin]

/-! ### Membership helpers -/

/-- Membership in `schurTriples`. -/
lemma schurTriples_mem {n : ℕ} (i j : Fin n) (h_le : i.val ≤ j.val)
    (h_k : i.val + j.val + 1 < n) :
    (i, j, ⟨i.val + j.val + 1, h_k⟩) ∈ schurTriples n := by
  unfold schurTriples
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_finRange i, ?_⟩
  rw [List.mem_filterMap]
  refine ⟨j, List.mem_finRange j, ?_⟩
  simp only [dif_pos h_le, dif_pos h_k]

/-- Properties recovered from `schurTriples` membership. -/
lemma schurTriples_spec {n : ℕ} (i j k : Fin n) (h : (i, j, k) ∈ schurTriples n) :
    i.val ≤ j.val ∧ k.val = i.val + j.val + 1 := by
  unfold schurTriples at h
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and] at h
  obtain ⟨i', ⟨j', h_filt⟩⟩ := h
  split at h_filt
  · rename_i h_le
    split at h_filt
    · rename_i h_lt
      simp only [Option.some.injEq, Prod.mk.injEq] at h_filt
      obtain ⟨rfl, rfl, h3⟩ := h_filt
      exact ⟨h_le, by simp [← h3]⟩
    · simp at h_filt
  · simp at h_filt

private lemma int_eq_of_toNat_eq {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a.toNat = b.toNat) :
    a = b := by
  have ha' := Int.toNat_of_nonneg ha
  have hb' := Int.toNat_of_nonneg hb
  omega

/-- A `schur_csp` solution keeps every variable in `[0, c-1]`. -/
lemma schur_csp_bounds {n c : ℕ} (a : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (schur_csp n c) a) (v : Fin n) :
    0 ≤ a v ∧ a v ≤ c - 1 := by
  have h_mem : bound v 0 (c - 1) ∈ (schur_csp n c).constraints := by
    unfold schur_csp schur_csp_triples schur_bound_constraints
    simp [List.mem_append, List.mem_map, List.mem_finRange]
  exact (bound_sat_iff v 0 (c - 1) a).mp (h_sol _ h_mem)

/-- A `schur_csp` solution satisfies every triple's not-all-equal constraint. -/
lemma schur_csp_triple {n c : ℕ} (a : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (schur_csp n c) a)
    (i j k : Fin n) (h_triple : (i, j, k) ∈ schurTriples n) :
    a i ≠ a j ∨ a i ≠ a k ∨ a j ≠ a k := by
  have h_mem : schur_triple i j k ∈ (schur_csp n c).constraints := by
    unfold schur_csp schur_csp_triples schur_triple_constraints
    simp only [List.mem_append, List.mem_map]
    right
    exact ⟨(i, j, k), h_triple, rfl⟩
  exact (schur_triple_sat_iff i j k a).mp (h_sol _ h_mem)

/-! ### Bridge theorem -/

/-- **Bridge:** the Schur CSP is satisfiable iff `{1,…,n}` is `c`-colourable sum-free. -/
theorem schur_csp_iff_colorable (n c : ℕ) :
    IntCSP.isSatisfiableInt (schur_csp n c) ↔ SchurColorable n c := by
  constructor
  · -- Forward: CSP solution → SchurColorable
    rintro ⟨a, h_sol⟩
    have h_bounds : ∀ v : Fin n, 0 ≤ a v ∧ a v ≤ c - 1 :=
      fun v => schur_csp_bounds a h_sol v
    refine ⟨fun v => ⟨(a v).toNat, ?_⟩, ?_⟩
    · have hv := h_bounds v
      have h_nn := hv.1
      have h_ub := hv.2
      have : a v < c := by linarith
      exact (Int.toNat_lt h_nn).mpr this
    · intro i j k ⟨hk, h_ij, h_jk⟩
      have h_ij' : (a i).toNat = (a j).toNat := Fin.val_eq_of_eq h_ij
      have h_jk' : (a j).toNat = (a k).toNat := Fin.val_eq_of_eq h_jk
      have h_a_ij : a i = a j :=
        int_eq_of_toNat_eq (h_bounds i).1 (h_bounds j).1 h_ij'
      have h_a_jk : a j = a k :=
        int_eq_of_toNat_eq (h_bounds j).1 (h_bounds k).1 h_jk'
      by_cases h_le : i.val ≤ j.val
      · have h_k_lt : i.val + j.val + 1 < n := by omega
        have h_k_fin : k = ⟨i.val + j.val + 1, h_k_lt⟩ := Fin.ext hk
        have h_triple := schurTriples_mem i j h_le h_k_lt
        have h_ne := schur_csp_triple a h_sol i j ⟨i.val + j.val + 1, h_k_lt⟩ h_triple
        rw [h_k_fin] at h_a_jk
        rcases h_ne with h | h | h
        · exact h h_a_ij
        · exact h (h_a_ij.trans h_a_jk)
        · exact h h_a_jk
      · push_neg at h_le
        have h_le' : j.val ≤ i.val := Nat.le_of_lt h_le
        have h_k_lt : j.val + i.val + 1 < n := by omega
        have h_k_fin : k = ⟨j.val + i.val + 1, h_k_lt⟩ :=
          Fin.ext (by show k.val = j.val + i.val + 1; omega)
        have h_triple := schurTriples_mem j i h_le' h_k_lt
        have h_ne := schur_csp_triple a h_sol j i ⟨j.val + i.val + 1, h_k_lt⟩ h_triple
        rw [h_k_fin] at h_a_jk
        rcases h_ne with h | h | h
        · exact h h_a_ij.symm
        · exact h h_a_jk
        · exact h (h_a_ij.trans h_a_jk)
  · -- Backward: SchurColorable → CSP solution
    rintro ⟨χ, h_χ⟩
    refine ⟨fun v => (χ v).val, ?_⟩
    intro tc h_tc
    unfold schur_csp schur_csp_triples at h_tc
    simp only [List.mem_append] at h_tc
    rcases h_tc with h_bound | h_triple
    · unfold schur_bound_constraints at h_bound
      simp only [List.mem_map, List.mem_finRange, true_and] at h_bound
      obtain ⟨v, h_eq⟩ := h_bound
      rw [← h_eq]
      apply (bound_sat_iff v 0 (↑c - 1) _).mpr
      refine ⟨Int.natCast_nonneg _, ?_⟩
      have hlt : ((χ v).val : ℤ) < (c : ℤ) := by exact_mod_cast (χ v).isLt
      linarith
    · unfold schur_triple_constraints at h_triple
      simp only [List.mem_map] at h_triple
      obtain ⟨⟨i, j, k⟩, h_mem, h_eq⟩ := h_triple
      rw [← h_eq]
      refine (schur_triple_sat_iff i j k _).mpr ?_
      have ⟨_, h_k_eq⟩ := schurTriples_spec i j k h_mem
      by_contra h_neg
      push_neg at h_neg
      obtain ⟨h1, h2, h3⟩ := h_neg
      apply h_χ i j k
      refine ⟨h_k_eq, ?_, ?_⟩
      · exact Fin.ext (Int.ofNat_inj.mp h1)
      · exact Fin.ext (Int.ofNat_inj.mp h3)

end Bridge

end Schur
