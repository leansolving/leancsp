import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Proofs.PatternBridges
import CSP.L2S.Proofs.SchurEquivalence
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange

open CSP.L2S

namespace Schur

/-!
## Schur Numbers Symmetry Breaking

### Problem
Variables: One per integer (n variables)
Domains: Colors (integers 0..c-1)
Constraints: For each valid triple (i,j,k), not all three have the same color (schur_triple)

### Symmetry Breaking
**Symmetry**: Color swap (Equiv.swap 0 c₀) for any color c₀ in [0, c-1]
**SBC**: Fix x₀ = 0 (first integer gets color 0) via equals_const ⟨0, _⟩ 0

### Results
1. Color swap is a domain symmetry for Schur CSP
2. SBC is a domain symmetry breaking constraint
3. SBC is a general symmetry breaking constraint
4. Extended CSP is equisatisfiable with original

This is the `CSP/L2S` port of the `CSP/Int` proof: the satisfaction reasoning goes
through `patternHolds`/`PatternBridges` and `satisfiesConstraintInt_iff_toDynamic`
instead of the dynamic-constraint checker.
-/

-- ============================================================================
-- CSP Definition (reuse from SchurEquivalence)
-- ============================================================================

/-- Bound constraints: each integer has a color in {0, ..., colors-1} -/
def schur_bound_constraints (n : ℕ) (colors : ℕ) : List (IntConstraint n) :=
  (List.finRange n).map (fun v => bound v 0 (colors - 1))

/-- Triple constraints: no monochromatic triple -/
def schur_triple_constraints (n : ℕ) (triples : List (Fin n × Fin n × Fin n)) : List (IntConstraint n) :=
  triples.map (fun ⟨i, j, k⟩ => schur_triple i j k)

/-- Schur CSP -/
def schur_csp_triples (n : ℕ) (colors : ℕ) (triples : List (Fin n × Fin n × Fin n)) : IntCSP :=
  ⟨n, schur_bound_constraints n colors ++ schur_triple_constraints n triples⟩

-- ============================================================================
-- Symmetry Breaking Constraint Definition
-- ============================================================================

/-- Symmetry breaking constraint: fix first integer to color 0 -/
def schur_sbc (n : ℕ) (h_n : 0 < n) : IntConstraint n :=
  equals_const ⟨0, h_n⟩ 0

/-- Extended CSP (including the SBC) -/
def schur_sb_triples (n : ℕ) (h_n : 0 < n) (colors : ℕ) (triples : List (Fin n × Fin n × Fin n)) : IntCSP :=
  (schur_csp_triples n colors triples).addConstraint (schur_sbc n h_n)

-- ============================================================================
-- Symmetry Function
-- ============================================================================

/-- Color swap: swaps color 0 with color c, leaves others unchanged -/
def schur_color_swap (c : ℤ) : Equiv.Perm IntDomain :=
  Equiv.swap 0 c

-- ============================================================================
-- Auxiliary Lemmas
-- ============================================================================

/-- Color swaps preserve the interval [0, colors-1] when c is in that interval -/
lemma intervalPreserving_schur_color_swap (colors : ℕ) (c : ℤ)
    (h_colors : 0 < colors)
    (h_c : 0 ≤ c ∧ c < colors) :
    intervalPreserving (schur_color_swap c) 0 (colors - 1) := by
  intro d
  unfold schur_color_swap
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_cases h1 : d = 0
    · simp [h1, Equiv.swap_apply_left]
      exact ⟨h_c.1, by omega⟩
    · by_cases h2 : d = c
      · simp [h2, Equiv.swap_apply_right]
        omega
      · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact ⟨h_lb, h_ub⟩
  · intro ⟨h_lb, h_ub⟩
    by_cases h1 : d = 0
    · omega
    · by_cases h2 : d = c
      · rw [h2]
        exact ⟨h_c.1, by omega⟩
      · simp [Equiv.swap_apply_of_ne_of_ne h1 h2] at h_lb h_ub
        exact ⟨h_lb, h_ub⟩

/-- Schur triple constraints are preserved by any domain permutation (due to injectivity) -/
lemma schur_triple_preserved_by_perm {num_vars : ℕ}
    (δ : Equiv.Perm IntDomain)
    (u v w : VarType num_vars) :
    taggedConstraintDomainSymmetric (schur_triple u v w) δ := by
  unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
  intro assignment h_sat
  rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
  rw [schur_triple_holds_iff] at h_sat ⊢
  simp only [Function.comp_apply] at h_sat ⊢
  rcases h_sat with h_ne | h_ne | h_ne
  · left; exact fun h_eq => h_ne (δ.injective h_eq)
  · right; left; exact fun h_eq => h_ne (δ.injective h_eq)
  · right; right; exact fun h_eq => h_ne (δ.injective h_eq)

-- ============================================================================
-- Symmetry-Breaking Correctness
-- ============================================================================

/-- Result 1: Color swap is a domain symmetry for Schur CSP -/
theorem schur_color_swap_is_symmetry (n colors : ℕ)
    (triples : List (Fin n × Fin n × Fin n)) (c : ℤ)
    (h_colors : 0 < colors)
    (h_c : 0 ≤ c ∧ c < colors) :
    DomainSymmetry (schur_csp_triples n colors triples) (schur_color_swap c) := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold schur_csp_triples at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  obtain h_bound | h_triple := h_tc_mem
  · unfold schur_bound_constraints at h_bound
    simp only [List.mem_map] at h_bound
    obtain ⟨v, _, h_eq⟩ := h_bound
    rw [← h_eq]
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
    have h_interval := intervalPreserving_schur_color_swap colors c h_colors h_c
    have h_preserves := intervalPreserving_preserves_bound (schur_color_swap c) v 0 (colors - 1) h_interval assignment
    exact h_preserves.mp h_sat
  · unfold schur_triple_constraints at h_triple
    simp only [List.mem_map] at h_triple
    obtain ⟨⟨u, v, w⟩, _, h_eq⟩ := h_triple
    rw [← h_eq]
    exact schur_triple_preserved_by_perm (schur_color_swap c) u v w

/-- Result 2: The symmetry breaking constraint is a domain symmetry breaking constraint -/
theorem schur_sbc_is_domain_symmetry_breaking (n colors : ℕ)
    (h_n : 0 < n) (h_colors : 0 < colors)
    (triples : List (Fin n × Fin n × Fin n)) :
    domainSymmetryBreakingConstraint
      (schur_csp_triples n colors triples)
      (schur_sbc n h_n) := by
  intro assignment h_sol
  by_cases h : assignment ⟨0, h_n⟩ = 0
  · -- Identity case: solution already satisfies the SBC
    use DomainSymmetry.identity
    constructor
    · exact DomainSymmetry.identity_is_symmetry _
    · intro tc h_tc_mem
      simp only [IntCSP.addConstraint] at h_tc_mem
      obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
      · rw [h_sbc]
        simp only [IntCSP.satisfiesConstraintInt, schur_sbc, equals_const, patternHolds,
          valAt, IntCSP.addConstraint, schur_csp_triples, h_n, dif_pos, Function.comp_apply,
          DomainSymmetry.identity, Equiv.refl_apply]
        exact h
      · unfold IntCSP.isSolutionInt at h_sol
        simp only [DomainSymmetry.identity]
        exact h_sol tc h_orig
  · -- Swap case: apply color swap to fix color of first integer
    let c := assignment ⟨0, h_n⟩
    have h_c_in_bounds : 0 ≤ c ∧ c < colors := by
      have h_bound : bound ⟨0, h_n⟩ 0 (colors - 1) ∈ (schur_csp_triples n colors triples).constraints := by
        unfold schur_csp_triples schur_bound_constraints
        simp only [List.mem_append, List.mem_map, List.mem_finRange]
        left
        use ⟨0, h_n⟩
      have h_sat_bound := (bound_holds_iff _ _ _ _).mp
        (h_sol (bound ⟨0, h_n⟩ 0 (colors - 1)) h_bound)
      refine ⟨h_sat_bound.1, ?_⟩
      have hub : assignment ⟨0, h_n⟩ ≤ (colors : ℤ) - 1 := h_sat_bound.2
      show assignment ⟨0, h_n⟩ < (colors : ℤ)
      exact Int.lt_of_le_sub_one hub
    use schur_color_swap c
    constructor
    · exact schur_color_swap_is_symmetry n colors triples c h_colors h_c_in_bounds
    · intro tc h_tc_mem
      simp only [IntCSP.addConstraint] at h_tc_mem
      obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
      · rw [h_sbc]
        simp only [IntCSP.satisfiesConstraintInt, schur_sbc, equals_const, patternHolds,
          valAt, IntCSP.addConstraint, schur_csp_triples, h_n, dif_pos, Function.comp_apply]
        show (schur_color_swap c) c = 0
        unfold schur_color_swap
        rw [Equiv.swap_apply_right]
      · have h_sym := schur_color_swap_is_symmetry n colors triples c h_colors h_c_in_bounds
        unfold DomainSymmetry at h_sym
        have h_sol_orig := h_sym assignment h_sol
        exact h_sol_orig tc h_orig

/-- Result 3: The symmetry breaking constraint is a general symmetry breaking constraint -/
theorem schur_sbc_is_symmetry_breaking (n colors : ℕ)
    (h_n : 0 < n) (h_colors : 0 < colors)
    (triples : List (Fin n × Fin n × Fin n)) :
    symmetryBreakingConstraint
      (schur_csp_triples n colors triples)
      (schur_sbc n h_n) := by
  left
  exact schur_sbc_is_domain_symmetry_breaking n colors h_n h_colors triples

/-- Result 4: Equisatisfiability - The extended CSP is equisatisfiable with the original -/
theorem schur_sb_equisatisfiability (n colors : ℕ)
    (h_n : 0 < n) (h_colors : 0 < colors)
    (triples : List (Fin n × Fin n × Fin n)) :
    equisatisfiable
      (schur_csp_triples n colors triples)
      (schur_sb_triples n h_n colors triples) := by
  apply domainSymmetryBreaking_equisatisfiability
  exact schur_sbc_is_domain_symmetry_breaking n colors h_n h_colors triples

-- ============================================================================
-- Instantiated Versions (triples computed from n)
-- ============================================================================

/-- Schur CSP with triples computed from n -/
def schur_csp (n colors : ℕ) : IntCSP :=
  schur_csp_triples n colors (schurTriples n)

/-- Extended Schur CSP with SBC, triples computed from n -/
def schur_sb (n : ℕ) (h_n : 0 < n) (colors : ℕ) : IntCSP :=
  schur_sb_triples n h_n colors (schurTriples n)

theorem schur_sb_equisatisfiability' (n colors : ℕ)
    (h_n : 0 < n) (h_colors : 0 < colors) :
    equisatisfiable (schur_csp n colors) (schur_sb n h_n colors) :=
  schur_sb_equisatisfiability n colors h_n h_colors (schurTriples n)

end Schur
