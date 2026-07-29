import CSP.L2S.Tests.lean.«34_ramsey»
import CSP.L2S.Proofs.SchurSB
import CSP.L2S.ValuePrecedence

/-!
# Value precedence for the Ramsey CSP

`ramsey_r33_csp n` is `bound · 0 1` (two interchangeable edge colours) plus `schur_triple`
(not-all-equal) constraints over the triangles — structurally identical to Schur.  So
`value_precedence 2` is a `domainSymmetryBreakingConstraint`.
-/

open CSP.L2S IntCSP

/-- **Interval-preserving colour permutations are domain symmetries of the Ramsey CSP.** -/
theorem ramsey_interval_perm_is_symmetry (n : ℕ) (δ : Equiv.Perm ℤ)
    (hδ : intervalPreserving δ 0 ((2 : ℤ) - 1)) :
    DomainSymmetry (ramsey_r33_csp n) δ := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold ramsey_r33_csp at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  obtain h_bound | h_triple := h_tc_mem
  · unfold ramsey_bounds at h_bound
    simp only [List.mem_map] at h_bound
    obtain ⟨v, _, h_eq⟩ := h_bound
    rw [← h_eq]
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
    exact (intervalPreserving_preserves_bound δ v 0 1 hδ assignment).mp h_sat
  · unfold ramsey_constraints at h_triple
    simp only [List.mem_filterMap] at h_triple
    obtain ⟨⟨e1, e2, e3⟩, _, h_eq⟩ := h_triple
    split_ifs at h_eq with h1 h2 h3
    · rw [← Option.some.inj h_eq]
      exact Schur.schur_triple_preserved_by_perm δ ⟨e1, h1⟩ ⟨e2, h2⟩ ⟨e3, h3⟩

/-- **Domain bound for the Ramsey CSP.** -/
theorem ramsey_hdom (n : ℕ) :
    ∀ b : IntAssignment (ramsey_num_edges n), isSolutionInt (ramsey_r33_csp n) b →
      ∀ j : Fin (ramsey_num_edges n), 0 ≤ b j ∧ b j ≤ (2 : ℤ) - 1 := by
  intro b hb j
  have hmem : bound j 0 1 ∈ (ramsey_r33_csp n).constraints := by
    unfold ramsey_r33_csp ramsey_bounds
    simp only [List.mem_append, List.mem_map]
    left; exact ⟨j, List.mem_finRange j, rfl⟩
  have hsat := hb _ hmem
  simp only [IntCSP.satisfiesConstraintInt, bound, patternHolds, ramsey_r33_csp, valAt, j.is_lt,
    dif_pos, Fin.eta] at hsat
  exact hsat

/-- **Value precedence is a domain symmetry-breaking constraint for the Ramsey CSP.** -/
theorem ramsey_value_precedence_is_sbc (n : ℕ) :
    domainSymmetryBreakingConstraint (ramsey_r33_csp n) (value_precedence 2) :=
  value_precedence_is_domain_symmetry_breaking (ramsey_r33_csp n) (ramsey_hdom n)
    (ramsey_interval_perm_is_symmetry n)

/-- **End-to-end bridge for the Ramsey CSP.** -/
theorem ramsey_unsat_of_value_precedence (n : ℕ)
    (h_unsat : ¬ isSatisfiableInt ((ramsey_r33_csp n).addConstraint (value_precedence 2))) :
    ¬ isSatisfiableInt (ramsey_r33_csp n) :=
  unsat_of_domain_sbc (ramsey_r33_csp n) (value_precedence 2) (ramsey_value_precedence_is_sbc n)
    h_unsat
