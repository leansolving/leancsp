import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.ValuePrecedence

/-!
# Value precedence for the Pigeonhole CSP

A 0-indexed pigeonhole CSP `php_csp pigeons holes` (each pigeon in a hole `[0, holes-1]`, all holes
distinct).  The holes are interchangeable, so every interval-preserving hole permutation is a
domain symmetry (bounds via `intervalPreserving_preserves_bound`; `alldifferent` via injectivity),
and `value_precedence holes` is a `domainSymmetryBreakingConstraint`.
-/

open CSP.L2S IntCSP

namespace Pigeonhole

/-- 0-indexed pigeonhole CSP: `pigeons` variables over holes `[0, holes-1]`, all distinct. -/
def php_csp (pigeons holes : ℕ) : IntCSP :=
  ⟨pigeons, (List.finRange pigeons).map (fun i => bound i 0 ((holes : ℤ) - 1)) ++
    [alldifferent (_root_.Vector.ofFn id)]⟩

/-- `alldifferent` over well-formed variables is preserved by any domain permutation (injectivity). -/
lemma alldifferent_preserved_by_perm {num_vars : ℕ} (δ : Equiv.Perm ℤ) (vars : List ℕ)
    (hwf : ∀ v ∈ vars, v < num_vars) :
    taggedConstraintDomainSymmetric (IntConstraint.alldifferent vars : IntConstraint num_vars) δ := by
  unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
  intro a h_sat
  rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
  simp only [IntCSP.satisfiesConstraintInt, patternHolds] at h_sat ⊢
  have hkey : vars.map (valAt (⇑δ ∘ a)) = (vars.map (valAt a)).map δ := by
    rw [List.map_map]
    apply List.map_congr_left
    intro v hv
    simp only [valAt, hwf v hv, dif_pos, Function.comp_apply]
  rw [hkey]
  exact List.Nodup.map δ.injective h_sat

/-- **Interval-preserving hole permutations are domain symmetries of the pigeonhole CSP.** -/
theorem php_interval_perm_is_symmetry (pigeons holes : ℕ) (δ : Equiv.Perm ℤ)
    (hδ : intervalPreserving δ 0 ((holes : ℤ) - 1)) :
    DomainSymmetry (php_csp pigeons holes) δ := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold php_csp at h_tc_mem
  simp only [List.mem_append, List.mem_singleton] at h_tc_mem
  obtain h_bound | h_alldiff := h_tc_mem
  · simp only [List.mem_map] at h_bound
    obtain ⟨v, _, h_eq⟩ := h_bound
    rw [← h_eq]
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
    exact (intervalPreserving_preserves_bound δ v 0 ((holes : ℤ) - 1) hδ assignment).mp h_sat
  · rw [h_alldiff]
    unfold alldifferent
    apply alldifferent_preserved_by_perm
    intro v hv
    simp only [List.mem_map] at hv
    obtain ⟨i, _, rfl⟩ := hv
    exact i.is_lt

/-- **Domain bound for the pigeonhole CSP.** -/
theorem php_hdom (pigeons holes : ℕ) :
    ∀ b : IntAssignment pigeons, isSolutionInt (php_csp pigeons holes) b →
      ∀ j : Fin pigeons, 0 ≤ b j ∧ b j ≤ (holes : ℤ) - 1 := by
  intro b hb j
  have hmem : bound j 0 ((holes : ℤ) - 1) ∈ (php_csp pigeons holes).constraints := by
    unfold php_csp
    simp only [List.mem_append, List.mem_map]
    left; exact ⟨j, List.mem_finRange j, rfl⟩
  have hsat := hb _ hmem
  simp only [IntCSP.satisfiesConstraintInt, bound, patternHolds, php_csp, valAt, j.is_lt,
    dif_pos, Fin.eta] at hsat
  exact hsat

/-- **Value precedence is a domain symmetry-breaking constraint for the pigeonhole CSP.** -/
theorem php_value_precedence_is_sbc (pigeons holes : ℕ) :
    domainSymmetryBreakingConstraint (php_csp pigeons holes) (value_precedence holes) :=
  value_precedence_is_domain_symmetry_breaking (php_csp pigeons holes) (php_hdom pigeons holes)
    (php_interval_perm_is_symmetry pigeons holes)

/-- **End-to-end bridge for the pigeonhole CSP.** -/
theorem php_unsat_of_value_precedence (pigeons holes : ℕ)
    (h_unsat : ¬ isSatisfiableInt ((php_csp pigeons holes).addConstraint (value_precedence holes))) :
    ¬ isSatisfiableInt (php_csp pigeons holes) :=
  unsat_of_domain_sbc (php_csp pigeons holes) (value_precedence holes)
    (php_value_precedence_is_sbc pigeons holes) h_unsat

end Pigeonhole
