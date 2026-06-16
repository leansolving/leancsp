import CSP.L2S.Tests.lean.«33_van_der_waerden»
import CSP.L2S.Proofs.SchurSB
import CSP.L2S.ValuePrecedence

/-!
# Value precedence for the Van der Waerden CSP

`vdw_csp n` is `bound · 0 1` (two interchangeable colours) plus `schur_triple` (not-all-equal)
constraints over the 3-APs — structurally identical to Schur.  So every interval-preserving colour
permutation is a domain symmetry (bounds via `intervalPreserving_preserves_bound`; AP triples via
`schur_triple_preserved_by_perm`), and `value_precedence 2` is a `domainSymmetryBreakingConstraint`.
-/

open CSP.L2S IntCSP

/-- **Interval-preserving colour permutations are domain symmetries of the VdW CSP.** -/
theorem vdw_interval_perm_is_symmetry (n : ℕ) (δ : Equiv.Perm ℤ)
    (hδ : intervalPreserving δ 0 ((2 : ℤ) - 1)) :
    DomainSymmetry (vdw_csp n) δ := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold vdw_csp at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  obtain h_bound | h_triple := h_tc_mem
  · unfold vdw_bounds at h_bound
    simp only [List.mem_map] at h_bound
    obtain ⟨v, _, h_eq⟩ := h_bound
    rw [← h_eq]
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
    exact (intervalPreserving_preserves_bound δ v 0 1 hδ assignment).mp h_sat
  · unfold vdw_constraints at h_triple
    simp only [List.mem_filterMap] at h_triple
    obtain ⟨⟨i, j, k⟩, _, h_eq⟩ := h_triple
    split_ifs at h_eq with h1 h2 h3
    · rw [← Option.some.inj h_eq]
      exact Schur.schur_triple_preserved_by_perm δ ⟨i, h1⟩ ⟨j, h2⟩ ⟨k, h3⟩

/-- **Domain bound for the VdW CSP.** -/
theorem vdw_hdom (n : ℕ) :
    ∀ b : IntAssignment n, isSolutionInt (vdw_csp n) b →
      ∀ j : Fin n, 0 ≤ b j ∧ b j ≤ (2 : ℤ) - 1 := by
  intro b hb j
  have hmem : bound j 0 1 ∈ (vdw_csp n).constraints := by
    unfold vdw_csp vdw_bounds
    simp only [List.mem_append, List.mem_map]
    left; exact ⟨j, List.mem_finRange j, rfl⟩
  have hsat := hb _ hmem
  simp only [IntCSP.satisfiesConstraintInt, bound, patternHolds, vdw_csp, valAt, j.is_lt,
    dif_pos, Fin.eta] at hsat
  exact hsat

/-- **Value precedence is a domain symmetry-breaking constraint for the VdW CSP.** -/
theorem vdw_value_precedence_is_sbc (n : ℕ) :
    domainSymmetryBreakingConstraint (vdw_csp n) (value_precedence 2) :=
  value_precedence_is_domain_symmetry_breaking (vdw_csp n) (vdw_hdom n)
    (vdw_interval_perm_is_symmetry n)

/-- **End-to-end bridge for the VdW CSP.** -/
theorem vdw_unsat_of_value_precedence (n : ℕ)
    (h_unsat : ¬ isSatisfiableInt ((vdw_csp n).addConstraint (value_precedence 2))) :
    ¬ isSatisfiableInt (vdw_csp n) :=
  unsat_of_domain_sbc (vdw_csp n) (value_precedence 2) (vdw_value_precedence_is_sbc n) h_unsat
