import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Proofs.PatternBridges
import CSP.L2S.Proofs.SudokuEquivalence
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange

open CSP.L2S
open LatinSquare Sudoku

namespace Sudoku

/-!
## Sudoku Symmetry Breaking: Fix cell (0,0) to value 0

Domain symmetry via value swap (`Equiv.swap 0 v₀`).
Value permutations preserve all alldifferent constraints via injectivity.

### Results
1. Value swap is a domain symmetry of `sudoku_csp`
2. SBC predicate: for any solution, a value swap makes cell (0,0) = 0
3. General SBC wrapper
4. Equisatisfiability of original and extended CSPs

This is the `CSP/L2S` port of the `CSP/Int` proof: the satisfaction reasoning goes through
`patternHolds`/`PatternBridges` and `satisfiesConstraintInt_iff_toDynamic` instead of the
dynamic-constraint checker.
-/

-- ============================================================================
-- Value Swap Definition
-- ============================================================================

/-- Value swap: swaps value 0 with value v₀ -/
def sudoku_value_swap (v₀ : ℤ) : Equiv.Perm IntDomain :=
  Equiv.swap 0 v₀

-- ============================================================================
-- General Lemma: Alldifferent preserved by domain permutation
-- ============================================================================

/-- Alldifferent constraints are preserved by any domain permutation (via injectivity) -/
lemma alldifferent_preserved_by_domain_perm {num_vars n : ℕ}
    (δ : Equiv.Perm IntDomain)
    (scope : _root_.Vector (VarType num_vars) n) :
    taggedConstraintDomainSymmetric (alldifferent scope) δ := by
  unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
  intro assignment h_sat
  rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
  rw [alldifferent_holds_iff] at h_sat ⊢
  rw [← List.map_map]
  exact h_sat.map δ.injective

-- ============================================================================
-- Sudoku SB Section
-- ============================================================================

section SudokuSB

variable {b : ℕ} (h_b : 0 < b)
include h_b

private lemma gs_pos : 0 < gridSize b := Nat.mul_pos h_b h_b

private lemma gs_sq_pos : 0 < gridSize b * gridSize b :=
  Nat.mul_pos (gs_pos h_b) (gs_pos h_b)

/-- SBC: fix cell (0,0) to value 0 -/
def sudoku_sb_constraint : IntConstraint (gridSize b * gridSize b) :=
  equals_const ⟨0, gs_sq_pos h_b⟩ 0

/-- Extended Sudoku CSP -/
def extended_sudoku_csp : IntCSP :=
  (sudoku_csp b).addConstraint (sudoku_sb_constraint h_b)

-- ============================================================================
-- Auxiliary: Interval Preservation
-- ============================================================================

/-- Value swap preserves [0, gridSize b - 1] -/
lemma intervalPreserving_sudoku_value_swap (v₀ : ℤ)
    (h_v₀ : 0 ≤ v₀ ∧ v₀ < gridSize b) :
    intervalPreserving (sudoku_value_swap v₀) 0 (gridSize b - 1) := by
  have h_gs : (0 : ℤ) < gridSize b := by exact_mod_cast gs_pos h_b
  intro d
  unfold sudoku_value_swap
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_cases h1 : d = 0
    · subst h1
      simp only [Equiv.swap_apply_left]
      exact ⟨h_v₀.1, by linarith⟩
    · by_cases h2 : d = v₀
      · subst h2
        simp only [Equiv.swap_apply_right]
        exact ⟨by linarith, by linarith⟩
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact ⟨h_lb, h_ub⟩
  · intro ⟨h_lb, h_ub⟩
    by_cases h1 : d = 0
    · subst h1
      exact ⟨le_refl 0, by linarith⟩
    · by_cases h2 : d = v₀
      · subst h2
        exact ⟨h_v₀.1, by linarith⟩
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2] at h_lb h_ub
        exact ⟨h_lb, h_ub⟩

-- ============================================================================
-- Result 1: Value swap is a domain symmetry
-- ============================================================================

/-- Value swap is a domain symmetry for sudoku_csp -/
theorem sudoku_value_swap_is_symmetry (v₀ : ℤ)
    (h_v₀ : 0 ≤ v₀ ∧ v₀ < gridSize b) :
    DomainSymmetry (sudoku_csp b) (sudoku_value_swap v₀) := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold sudoku_csp at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  rcases h_tc_mem with ((h_bound | h_row) | h_col) | h_box
  · -- Bounds
    unfold bound_constraints at h_bound
    simp only [List.mem_map, List.mem_finRange, true_and] at h_bound
    obtain ⟨v, rfl⟩ := h_bound
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢
    have h_interval := intervalPreserving_sudoku_value_swap h_b v₀ h_v₀
    exact (intervalPreserving_preserves_bound (sudoku_value_swap v₀) v 0
      (gridSize b - 1) h_interval assignment).mp h_sat
  · -- Row alldifferent
    unfold row_constraints at h_row
    simp only [List.mem_map, List.mem_finRange, true_and] at h_row
    obtain ⟨r, rfl⟩ := h_row
    exact alldifferent_preserved_by_domain_perm (sudoku_value_swap v₀) (row_variables r)
  · -- Col alldifferent
    unfold col_constraints at h_col
    simp only [List.mem_map, List.mem_finRange, true_and] at h_col
    obtain ⟨c, rfl⟩ := h_col
    exact alldifferent_preserved_by_domain_perm (sudoku_value_swap v₀) (col_variables c)
  · -- Box alldifferent
    unfold box_constraints at h_box
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at h_box
    obtain ⟨bi, bj, rfl⟩ := h_box
    exact alldifferent_preserved_by_domain_perm (sudoku_value_swap v₀) (box_variables b bi bj)

-- ============================================================================
-- Result 2: SBC predicate
-- ============================================================================

/-- The SBC is a domain symmetry breaking constraint -/
theorem sudoku_sb_is_domain_symmetry_breaking :
    domainSymmetryBreakingConstraint
      (sudoku_csp b)
      (sudoku_sb_constraint h_b) := by
  intro assignment h_sol
  by_cases h : assignment ⟨0, gs_sq_pos h_b⟩ = 0
  · -- Already satisfies SBC: use identity
    use DomainSymmetry.identity
    constructor
    · exact DomainSymmetry.identity_is_symmetry _
    · intro tc h_tc_mem
      simp only [IntCSP.addConstraint] at h_tc_mem
      obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
      · rw [h_sbc]
        simp only [IntCSP.satisfiesConstraintInt, sudoku_sb_constraint, equals_const, patternHolds,
          valAt, IntCSP.addConstraint, sudoku_csp, gs_sq_pos h_b, dif_pos, Function.comp_apply,
          DomainSymmetry.identity, Equiv.refl_apply]
        exact h
      · exact h_sol tc h_orig
  · -- Apply value swap
    let v₀ := assignment ⟨0, gs_sq_pos h_b⟩
    have h_v₀_bounds : 0 ≤ v₀ ∧ v₀ < gridSize b :=
      ls_compact_bounds assignment (sudoku_sol_is_ls_sol assignment h_sol) ⟨0, gs_sq_pos h_b⟩
    use sudoku_value_swap v₀
    constructor
    · exact sudoku_value_swap_is_symmetry h_b v₀ h_v₀_bounds
    · intro tc h_tc_mem
      simp only [IntCSP.addConstraint] at h_tc_mem
      obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
      · rw [h_sbc]
        simp only [IntCSP.satisfiesConstraintInt, sudoku_sb_constraint, equals_const, patternHolds,
          valAt, IntCSP.addConstraint, sudoku_csp, gs_sq_pos h_b, dif_pos, Function.comp_apply]
        show (sudoku_value_swap v₀) v₀ = 0
        unfold sudoku_value_swap
        rw [Equiv.swap_apply_right]
      · have h_sym := sudoku_value_swap_is_symmetry h_b v₀ h_v₀_bounds
        unfold DomainSymmetry at h_sym
        exact (h_sym assignment h_sol) tc h_orig

-- ============================================================================
-- Result 3: General SBC wrapper
-- ============================================================================

/-- General symmetry breaking constraint -/
theorem sudoku_sb_is_symmetry_breaking :
    symmetryBreakingConstraint
      (sudoku_csp b)
      (sudoku_sb_constraint h_b) := by
  left
  exact sudoku_sb_is_domain_symmetry_breaking h_b

-- ============================================================================
-- Result 4: Equisatisfiability
-- ============================================================================

/-- Equisatisfiability of original and extended CSPs -/
theorem sudoku_sb_equisatisfiability :
    equisatisfiable
      (sudoku_csp b)
      (extended_sudoku_csp h_b) := by
  apply domainSymmetryBreaking_equisatisfiability
  exact sudoku_sb_is_domain_symmetry_breaking h_b

end SudokuSB

end Sudoku
