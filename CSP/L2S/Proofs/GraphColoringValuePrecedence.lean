import CSP.L2S.Proofs.GraphColoringSB
import CSP.L2S.ValuePrecedence

/-!
# Value precedence for graph colouring

Discharges the hypotheses of `value_precedence_is_domain_symmetry_breaking` for
`graph_coloring_csp`: every interval-preserving colour permutation is a domain symmetry
(bounds are preserved by `intervalPreserving_preserves_bound`, edges by injectivity), and
every solution colours in `[0, colors-1]`.  Hence `value_precedence colors` is a
`domainSymmetryBreakingConstraint` and `unsat_of_domain_sbc` transports UNSAT.
-/

open CSP.L2S IntCSP

/-- **Interval-preserving colour permutations are domain symmetries of the colouring CSP.** -/
theorem graph_coloring_interval_perm_is_symmetry (nodes colors : ℕ)
    (edges : List (Fin nodes × Fin nodes)) (δ : Equiv.Perm ℤ)
    (hδ : intervalPreserving δ 0 ((colors : ℤ) - 1)) :
    DomainSymmetry (graph_coloring_csp nodes edges colors) δ := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold graph_coloring_csp at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  obtain h_bound | h_edge := h_tc_mem
  · unfold bound_constraints at h_bound
    simp only [List.mem_map] at h_bound
    obtain ⟨v, _, h_eq⟩ := h_bound
    rw [← h_eq]
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
    exact (intervalPreserving_preserves_bound δ v 0 (colors - 1) hδ assignment).mp h_sat
  · unfold edge_constraints at h_edge
    simp only [List.mem_map] at h_edge
    obtain ⟨⟨u, v⟩, _, h_eq⟩ := h_edge
    rw [← h_eq]
    exact not_equal_preserved_by_swap δ u v

/-- **Domain bound.**  Every colouring uses values in `[0, colors-1]`. -/
theorem graph_coloring_hdom (nodes colors : ℕ) (edges : List (Fin nodes × Fin nodes)) :
    ∀ b : IntAssignment nodes, isSolutionInt (graph_coloring_csp nodes edges colors) b →
      ∀ j : Fin nodes, 0 ≤ b j ∧ b j ≤ (colors : ℤ) - 1 := by
  intro b hb j
  have hmem : bound j 0 (colors - 1) ∈ (graph_coloring_csp nodes edges colors).constraints := by
    unfold graph_coloring_csp bound_constraints
    simp only [List.mem_append, List.mem_map]
    left; exact ⟨j, List.mem_finRange j, rfl⟩
  have hsat := hb _ hmem
  simp only [IntCSP.satisfiesConstraintInt, bound, patternHolds, graph_coloring_csp, valAt,
    j.is_lt, dif_pos, Fin.eta] at hsat
  exact hsat

/-- **Value precedence is a domain symmetry-breaking constraint for graph colouring.** -/
theorem graph_coloring_value_precedence_is_sbc (nodes colors : ℕ)
    (edges : List (Fin nodes × Fin nodes)) :
    domainSymmetryBreakingConstraint (graph_coloring_csp nodes edges colors)
      (value_precedence colors) :=
  value_precedence_is_domain_symmetry_breaking (graph_coloring_csp nodes edges colors)
    (graph_coloring_hdom nodes colors edges)
    (graph_coloring_interval_perm_is_symmetry nodes colors edges)

/-- **End-to-end bridge.**  UNSAT of the value-precedence-extended colouring CSP yields UNSAT of
    the original. -/
theorem graph_coloring_unsat_of_value_precedence (nodes colors : ℕ)
    (edges : List (Fin nodes × Fin nodes))
    (h_unsat : ¬ isSatisfiableInt
      ((graph_coloring_csp nodes edges colors).addConstraint (value_precedence colors))) :
    ¬ isSatisfiableInt (graph_coloring_csp nodes edges colors) :=
  unsat_of_domain_sbc (graph_coloring_csp nodes edges colors) (value_precedence colors)
    (graph_coloring_value_precedence_is_sbc nodes colors edges) h_unsat
