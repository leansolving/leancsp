import CSP.L2S.Proofs.SchurSB
import CSP.L2S.ValuePrecedence

/-!
# Value precedence for the Schur CSP

Discharges the two hypotheses of `value_precedence_is_domain_symmetry_breaking` for the Schur CSP:

* **`schur_hdom`** — every solution colours `{1,…,n}` with values in `[0, colors-1]` (the bounds);
* **`schur_interval_perm_is_symmetry`** — every interval-preserving colour permutation is a domain
  symmetry (bounds are interval-preserving via `intervalPreserving_preserves_bound`; triples are
  preserved by *any* permutation via injectivity, `schur_triple_preserved_by_perm`).

Hence `value_precedence colors` is a `domainSymmetryBreakingConstraint` for the Schur CSP, and the
project's symmetry-breaking machinery (`domainSymmetryBreaking_equisatisfiability`,
`unsat_of_domain_sbc`) yields UNSAT of the original CSP from a PB certificate of the extended one.
-/

open CSP.L2S IntCSP

namespace Schur

/-- **Interval-preserving colour permutations are domain symmetries of the Schur CSP.** -/
theorem schur_interval_perm_is_symmetry (n colors : ℕ) (triples : List (Fin n × Fin n × Fin n))
    (δ : Equiv.Perm ℤ) (hδ : intervalPreserving δ 0 ((colors : ℤ) - 1)) :
    DomainSymmetry (schur_csp_sb n colors triples) δ := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold schur_csp_sb at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  obtain h_bound | h_triple := h_tc_mem
  · unfold schur_bound_constraints at h_bound
    simp only [List.mem_map] at h_bound
    obtain ⟨v, _, h_eq⟩ := h_bound
    rw [← h_eq]
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
    exact (intervalPreserving_preserves_bound δ v 0 (colors - 1) hδ assignment).mp h_sat
  · unfold schur_triple_constraints at h_triple
    simp only [List.mem_map] at h_triple
    obtain ⟨⟨u, v, w⟩, _, h_eq⟩ := h_triple
    rw [← h_eq]
    exact schur_triple_preserved_by_perm δ u v w

/-- **Domain bound for the Schur CSP.**  Every solution colours each integer in `[0, colors-1]`. -/
theorem schur_hdom (n colors : ℕ) (triples : List (Fin n × Fin n × Fin n)) :
    ∀ b : IntAssignment n, isSolutionInt (schur_csp_sb n colors triples) b →
      ∀ j : Fin n, 0 ≤ b j ∧ b j ≤ (colors : ℤ) - 1 := by
  intro b hb j
  have hmem : bound j 0 (colors - 1) ∈ (schur_csp_sb n colors triples).constraints := by
    unfold schur_csp_sb schur_bound_constraints
    simp only [List.mem_append, List.mem_map]
    left; exact ⟨j, List.mem_finRange j, rfl⟩
  have hsat := hb _ hmem
  simp only [IntCSP.satisfiesConstraintInt, bound, patternHolds, schur_csp_sb, valAt, j.is_lt,
    dif_pos, Fin.eta] at hsat
  exact hsat

/-- **Value precedence is a domain symmetry-breaking constraint for the Schur CSP.** -/
theorem schur_value_precedence_is_sbc (n colors : ℕ) (triples : List (Fin n × Fin n × Fin n)) :
    domainSymmetryBreakingConstraint (schur_csp_sb n colors triples) (value_precedence colors) :=
  value_precedence_is_domain_symmetry_breaking (schur_csp_sb n colors triples)
    (schur_hdom n colors triples) (schur_interval_perm_is_symmetry n colors triples)

/-- **End-to-end bridge.**  UNSAT of the value-precedence-extended Schur CSP yields UNSAT of the
    original Schur CSP — through the project's `unsat_of_domain_sbc` machinery. -/
theorem schur_unsat_of_value_precedence (n colors : ℕ)
    (triples : List (Fin n × Fin n × Fin n))
    (h_unsat : ¬ isSatisfiableInt
      ((schur_csp_sb n colors triples).addConstraint (value_precedence colors))) :
    ¬ isSatisfiableInt (schur_csp_sb n colors triples) :=
  unsat_of_domain_sbc (schur_csp_sb n colors triples) (value_precedence colors)
    (schur_value_precedence_is_sbc n colors triples) h_unsat

/-- **Full equisatisfiability** of the Schur CSP and its value-precedence extension — the SAT
    counterpart of `schur_unsat_of_value_precedence`, used to lift a witness of the extended
    CSP back to a satisfiability proof of the original. -/
theorem schur_vp_equisatisfiability (n colors : ℕ) (triples : List (Fin n × Fin n × Fin n)) :
    equisatisfiable (schur_csp_sb n colors triples)
      ((schur_csp_sb n colors triples).addConstraint (value_precedence colors)) :=
  domainSymmetryBreaking_equisatisfiability (schur_csp_sb n colors triples)
    (value_precedence colors) (schur_value_precedence_is_sbc n colors triples)

/-- `schur_sb`-specialised value-precedence equisatisfiability (triples computed from `n`). -/
theorem schur_vp_equisatisfiability' (n colors : ℕ) :
    equisatisfiable (schur_sb n colors)
      ((schur_sb n colors).addConstraint (value_precedence colors)) :=
  schur_vp_equisatisfiability n colors (schurTriples n)

end Schur
