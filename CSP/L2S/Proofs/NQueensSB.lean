import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Translate
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith

open CSP.L2S

/-!
## N-Queens problem

Variables: One per column (n)
Domains: Rows of the corresponding queens
Constraints: Different queens must be in different rows, columns and diagonals
-/

-- ============================================================================
-- CSP Definition
-- ============================================================================

/- Bound constraints -/
def bound_constraints (n : ℕ) : List (TaggedConstraint n) :=
  (List.finRange n).map (fun v => bound v 0 (n-1))

/- All queens must be placed in different rows -/
def row_constraint (n : ℕ) : TaggedConstraint n :=
  alldifferent_all n

/- All queens must be placed in different diagonals (x[i] - i all different) -/
def diagonal_constraint (n : ℕ) : TaggedConstraint n :=
  alldifferent_diag_neg n

/- All queens must be placed in different antidiagonals (x[i] + i all different) -/
def antidiagonal_constraint (n : ℕ) : TaggedConstraint n :=
  alldifferent_diag_pos n

/- CSP: include all constraints -/
def nqueens_csp (n : ℕ) : HomogeneousCSP :=
  ⟨ n,
    bound_constraints n ++
    [row_constraint n] ++
    [diagonal_constraint n] ++
    [antidiagonal_constraint n] ⟩

-- ============================================================================
-- Symmetry Breaking Constraint Definition
-- ============================================================================

/- Our candidate to symmetry breaking constraint: first queen must be placed
on the first half of the first column -/
def sb_constraint (n : ℕ) (h_n : 0 < n) : TaggedConstraint n :=
  less_than_const ⟨0, h_n⟩ ((n + 1) / 2)

/- Extended CSP -/
def extended_nqueens_csp (n : ℕ) (h_n : 0 < n) : HomogeneousCSP :=
  (nqueens_csp n).addConstraint (sb_constraint n h_n)

-- ============================================================================
-- Symmetry Function
-- ============================================================================

/-- Horizontal reflection: maps row i to row (n-1) - i
    This is an involution (self-inverse permutation) -/
def horizontal_reflection (n : ℕ) : Equiv.Perm HomogeneousDomain where
  toFun := fun d => (↑n - 1 : ℤ) - d
  invFun := fun d => (↑n - 1 : ℤ) - d  -- involution: applying twice gives identity
  left_inv := fun d => by ring
  right_inv := fun d => by ring

-- ============================================================================
-- Auxiliary Lemmas
-- ============================================================================

/-- Horizontal reflection preserves the interval [0, n-1] -/
lemma intervalPreserving_horizontal_reflection (n : ℕ) :
    intervalPreserving (horizontal_reflection n) 0 (↑n - 1) := by
  intro d
  simp only [horizontal_reflection, Equiv.coe_fn_mk]
  show (0 ≤ d ∧ d ≤ ↑n - 1) ↔ (0 ≤ (↑n - 1 : ℤ) - d ∧ (↑n - 1 : ℤ) - d ≤ ↑n - 1)
  constructor
  · intro ⟨h_lb, h_ub⟩
    constructor <;> omega
  · intro ⟨h_lb, h_ub⟩
    constructor <;> omega

/-- Alldifferent_all is preserved by any permutation (via injectivity) -/
lemma alldifferent_all_preserved_by_perm {num_vars : ℕ}
    (δ : Equiv.Perm HomogeneousDomain) :
    taggedConstraintDomainSymmetric (alldifferent_all num_vars) δ := by
  unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
  intro assignment h_sat
  unfold alldifferent_all alldifferent CSP.satisfies_dynamic_constraint at *
  unfold CSP.satisfies_constraint CSP.sat at *
  simp only [decide_eq_true_iff] at *
  unfold extractValues at *
  have h_simp1 : ∀ i, CSP.map_assignment assignment (_root_.Vector.ofFn id) i = assignment i := by
    intro i
    simp [CSP.map_assignment, _root_.Vector.ofFn, _root_.Vector.get]
  have h_simp2 : ∀ i, CSP.map_assignment (δ ∘ assignment) (_root_.Vector.ofFn id) i = δ (assignment i) := by
    intro i
    simp [CSP.map_assignment, _root_.Vector.ofFn, _root_.Vector.get, Function.comp_apply]
  simp only [h_simp1] at h_sat
  simp only [h_simp2]
  have h_eq : (fun i : Fin num_vars => δ (assignment i)) = (δ ∘ assignment) := by
    funext i; rfl
  rw [h_eq]
  have h_map : List.ofFn (δ ∘ assignment) = (List.ofFn assignment).map δ := by
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp [Function.comp_apply]
  rw [h_map]
  exact List.Nodup.map δ.injective h_sat

/-- Diagonal constraints: key algebraic identity for positive diagonal swapping -/
lemma diag_pos_identity (n : ℕ) (x i : ℤ) :
    ((↑n - 1 : ℤ) - x) + i = (↑n - 1 : ℤ) - (x - i) := by
  ring

/-- Diagonal constraints: key algebraic identity for negative diagonal swapping -/
lemma diag_neg_identity (n : ℕ) (x i : ℤ) :
    ((↑n - 1 : ℤ) - x) - i = (↑n - 1 : ℤ) - (x + i) := by
  ring

/-- Affine transformations preserve List.Nodup -/
lemma affine_transform_preserves_nodup (L : List ℤ) (a : ℤ) :
    L.Nodup → (L.map (fun x => a - x)).Nodup := by
  intro h
  have h_inj : Function.Injective (fun x : ℤ => a - x) := fun x y hxy => by linarith
  exact List.Nodup.map h_inj h

/-- Diagonal constraints swap under horizontal reflection -/
lemma diagonal_constraints_swap (n : ℕ)
    (assignment : HomogeneousAssignment n)
    (h_pos_sat : HomogeneousCSP.satisfiesConstraint (alldifferent_diag_pos n) assignment)
    (h_neg_sat : HomogeneousCSP.satisfiesConstraint (alldifferent_diag_neg n) assignment) :
    HomogeneousCSP.satisfiesConstraint (alldifferent_diag_pos n) ((horizontal_reflection n) ∘ assignment) ∧
    HomogeneousCSP.satisfiesConstraint (alldifferent_diag_neg n) ((horizontal_reflection n) ∘ assignment) := by
  have h_map_id : ∀ (a : HomogeneousAssignment n) (i : Fin n),
    CSP.map_assignment a (_root_.Vector.ofFn (fun j : Fin n => j)) i = a i := by
    intros a i
    simp [CSP.map_assignment, _root_.Vector.ofFn, _root_.Vector.get]

  have h_pos_nodup : (List.ofFn fun (i : Fin n) => assignment i + ↑i.val).Nodup := by
    unfold HomogeneousCSP.satisfiesConstraint alldifferent_diag_pos at h_pos_sat
    unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.sat at h_pos_sat
    simp only [decide_eq_true_iff, h_map_id] at h_pos_sat
    exact h_pos_sat

  have h_neg_nodup : (List.ofFn fun (i : Fin n) => assignment i - ↑i.val).Nodup := by
    unfold HomogeneousCSP.satisfiesConstraint alldifferent_diag_neg at h_neg_sat
    unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.sat at h_neg_sat
    simp only [decide_eq_true_iff, h_map_id] at h_neg_sat
    exact h_neg_sat

  constructor

  · unfold HomogeneousCSP.satisfiesConstraint alldifferent_diag_pos
    unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.sat
    simp only [decide_eq_true_iff, h_map_id]

    have h_eq : ∀ i : Fin n,
      ((horizontal_reflection n) ∘ assignment) i + ↑i.val = (↑n - 1 : ℤ) - (assignment i - ↑i.val) := by
      intro i
      simp [horizontal_reflection, Function.comp_apply]
      ring

    have : List.ofFn (fun i : Fin n => ((horizontal_reflection n) ∘ assignment) i + ↑i.val) =
           List.ofFn (fun i : Fin n => (↑n - 1 : ℤ) - (assignment i - ↑i.val)) := by
      simp_rw [h_eq]

    rw [this]
    have h_map_ofFn : List.ofFn (fun i : Fin n => (↑n - 1 : ℤ) - (assignment i - ↑i.val)) =
                      (List.ofFn fun i : Fin n => assignment i - ↑i.val).map (fun x => (↑n - 1 : ℤ) - x) := by
      apply List.ext_get
      · simp
      · intro i h1 h2
        simp

    rw [h_map_ofFn]
    exact affine_transform_preserves_nodup (List.ofFn fun i : Fin n => assignment i - ↑i.val) (↑n - 1) h_neg_nodup

  · unfold HomogeneousCSP.satisfiesConstraint alldifferent_diag_neg
    unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.sat
    simp only [decide_eq_true_iff, h_map_id]

    have h_eq : ∀ i : Fin n,
      ((horizontal_reflection n) ∘ assignment) i - ↑i.val = (↑n - 1 : ℤ) - (assignment i + ↑i.val) := by
      intro i
      simp [horizontal_reflection, Function.comp_apply]
      ring

    have : List.ofFn (fun i : Fin n => ((horizontal_reflection n) ∘ assignment) i - ↑i.val) =
           List.ofFn (fun i : Fin n => (↑n - 1 : ℤ) - (assignment i + ↑i.val)) := by
      simp_rw [h_eq]

    rw [this]
    have h_map_ofFn : List.ofFn (fun i : Fin n => (↑n - 1 : ℤ) - (assignment i + ↑i.val)) =
                      (List.ofFn fun i : Fin n => assignment i + ↑i.val).map (fun x => (↑n - 1 : ℤ) - x) := by
      apply List.ext_get
      · simp
      · intro i h1 h2
        simp

    rw [h_map_ofFn]
    exact affine_transform_preserves_nodup (List.ofFn fun i : Fin n => assignment i + ↑i.val) (↑n - 1) h_pos_nodup

-- ============================================================================
-- Symmetry-Breaking Correctness
-- ============================================================================

/-- Result 1: Horizontal reflection is a domain symmetry for N-Queens -/
theorem horizontal_reflection_is_symmetry (n : ℕ) :
    DomainSymmetry (nqueens_csp n) (horizontal_reflection n) := by
  intro assignment h_sol tc h_tc_mem
  have h_tc_orig := h_tc_mem
  unfold nqueens_csp bound_constraints at h_tc_mem
  simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_cons] at h_tc_mem
  rcases h_tc_mem with ((⟨v, _, h1⟩ | h2 | h3)| (h4 | h5)) | h6 | h7

  · subst h1
    unfold HomogeneousCSP.satisfiesConstraint
    have h_interval := intervalPreserving_horizontal_reflection n
    have h_preserves := intervalPreserving_preserves_bound (horizontal_reflection n) v 0 (↑n - 1) h_interval assignment
    have h_sat := h_sol (bound v 0 (↑n - 1)) h_tc_orig
    unfold HomogeneousCSP.satisfiesConstraint at h_sat
    exact h_preserves.mp h_sat

  · subst h2
    unfold row_constraint
    have h_sat := h_sol (row_constraint n) h_tc_orig
    exact alldifferent_all_preserved_by_perm (horizontal_reflection n) assignment h_sat

  · cases h3

  · subst h4
    unfold diagonal_constraint
    have h_pos_mem : antidiagonal_constraint n ∈ (nqueens_csp n).constraints := by
      unfold nqueens_csp
      simp [List.mem_append]
    have h_neg_mem : diagonal_constraint n ∈ (nqueens_csp n).constraints := by
      unfold nqueens_csp
      simp [List.mem_append]
    have h_pos_sat := h_sol (antidiagonal_constraint n) h_pos_mem
    have h_neg_sat := h_sol (diagonal_constraint n) h_neg_mem
    unfold antidiagonal_constraint at h_pos_sat
    unfold diagonal_constraint at h_neg_sat
    have h_swap := diagonal_constraints_swap n assignment h_pos_sat h_neg_sat
    exact h_swap.2

  · cases h5

  · subst h6
    unfold antidiagonal_constraint
    have h_pos_mem : antidiagonal_constraint n ∈ (nqueens_csp n).constraints := by
      unfold nqueens_csp
      simp [List.mem_append]
    have h_neg_mem : diagonal_constraint n ∈ (nqueens_csp n).constraints := by
      unfold nqueens_csp
      simp [List.mem_append]
    have h_pos_sat := h_sol (antidiagonal_constraint n) h_pos_mem
    have h_neg_sat := h_sol (diagonal_constraint n) h_neg_mem
    unfold antidiagonal_constraint at h_pos_sat
    unfold diagonal_constraint at h_neg_sat
    have h_swap := diagonal_constraints_swap n assignment h_pos_sat h_neg_sat
    exact h_swap.1

  · cases h7

/-- Result 2: The symmetry breaking constraint is a domain symmetry breaking constraint -/
theorem sb_constraint_is_domain_symmetry_breaking (n : ℕ) (h_n : 0 < n) :
    domainSymmetryBreakingConstraint (nqueens_csp n) (sb_constraint n h_n) := by
  intro assignment h_sol
  by_cases h : assignment ⟨0, h_n⟩ < ((↑n + 1) / 2 : ℤ)
  · use DomainSymmetry.identity
    constructor
    · exact DomainSymmetry.identity_is_symmetry _
    · intro tc h_tc_mem
      simp only [HomogeneousCSP.addConstraint] at h_tc_mem
      obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
      · rw [h_sbc]
        unfold HomogeneousCSP.satisfiesConstraint sb_constraint less_than_const
        unfold CSP.satisfies_dynamic_constraint CSP.unary_dynamic_constraint
        unfold CSP.satisfies_constraint CSP.sat CSP.unary_constraint CSP.map_assignment
        simp only [_root_.Vector.get, decide_eq_true_iff, Function.comp_apply]
        simp only [DomainSymmetry.identity, Equiv.refl_apply]
        exact h
      · unfold HomogeneousCSP.isSolution at h_sol
        simp only [DomainSymmetry.identity]
        exact h_sol tc h_orig
  · use horizontal_reflection n
    constructor
    · exact horizontal_reflection_is_symmetry n
    · intro tc h_tc_mem
      simp only [HomogeneousCSP.addConstraint] at h_tc_mem
      obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
      · rw [h_sbc]
        unfold HomogeneousCSP.satisfiesConstraint sb_constraint less_than_const
        unfold CSP.satisfies_dynamic_constraint CSP.unary_dynamic_constraint
        unfold CSP.satisfies_constraint CSP.sat CSP.unary_constraint CSP.map_assignment
        simp only [_root_.Vector.get, decide_eq_true_iff, Function.comp_apply]
        show (horizontal_reflection n) (assignment ⟨0, h_n⟩) < ((↑n + 1) / 2 : ℤ)
        unfold horizontal_reflection
        simp only [Equiv.coe_fn_mk]

        have h_bound_mem : bound ⟨0, h_n⟩ 0 (↑n - 1) ∈ (nqueens_csp n).constraints := by
          unfold nqueens_csp bound_constraints
          simp [List.mem_append, List.mem_map, List.mem_finRange]

        have h_bound_sat := h_sol _ h_bound_mem

        have h_upper : assignment ⟨0, h_n⟩ ≤ ↑n - 1 := by
          unfold HomogeneousCSP.satisfiesConstraint bound at h_bound_sat
          unfold CSP.satisfies_dynamic_constraint at h_bound_sat
          simp only [CSP.satisfies_constraint, CSP.sat, CSP.map_assignment, extractValues, _root_.Vector.get, List.ofFn] at h_bound_sat
          have : decide (0 ≤ assignment ⟨0, h_n⟩ ∧ assignment ⟨0, h_n⟩ ≤ ↑n - 1) = true := h_bound_sat
          simp only [decide_eq_true_iff] at this
          exact this.2

        have h_div_prop : ∀ m : ℤ, m / 2 * 2 ≤ m ∧ m ≤ m / 2 * 2 + 1 := by
          intro m
          have := Int.emod_two_eq_zero_or_one m
          omega

        have h_ge : assignment ⟨0, h_n⟩ >= (↑n + 1) / 2 := by
          by_contra h_contra
          push_neg at h_contra
          exact h h_contra

        have h_div_lower : (↑n + 1 : ℤ) / 2 * 2 ≤ ↑n + 1 := by
          exact (h_div_prop (↑n + 1)).1

        have h_div_upper : (↑n + 1 : ℤ) ≤ (↑n + 1) / 2 * 2 + 1 := by
          exact (h_div_prop (↑n + 1)).2

        have h_2x_ge : 2 * assignment ⟨0, h_n⟩ ≥ ↑n := by
          calc 2 * assignment ⟨0, h_n⟩
              ≥ 2 * ((↑n + 1) / 2) := by linarith [h_ge]
            _ ≥ (↑n + 1) - 1       := by linarith [h_div_lower]
            _ = ↑n                 := by ring

        have h_goal : 2 * ((↑n - 1 : ℤ) - assignment ⟨0, h_n⟩) < (↑n + 1 : ℤ) := by
          calc 2 * ((↑n - 1 : ℤ) - assignment ⟨0, h_n⟩)
              = 2 * (↑n : ℤ) - 2 - 2 * assignment ⟨0, h_n⟩  := by ring
            _ ≤ 2 * (↑n : ℤ) - 2 - ↑n                        := by linarith [h_2x_ge]
            _ = ↑n - 2                                        := by ring
            _ < ↑n + 1                                        := by omega

        have h_2y_le : 2 * ((↑n - 1 : ℤ) - assignment ⟨0, h_n⟩) ≤ ↑n := by omega

        have : (↑n - 1 : ℤ) - assignment ⟨0, h_n⟩ < ((↑n + 1) : ℤ) / 2 := by
          by_contra h_contra
          push_neg at h_contra
          have h1 : 2 * ((↑n - 1 : ℤ) - assignment ⟨0, h_n⟩) ≥ 2 * ((↑n + 1) / 2) := by linarith
          have h2 : 2 * ((↑n + 1) / 2) ≥ ↑n := by linarith [h_div_upper]
          have h3 : 2 * ((↑n - 1 : ℤ) - assignment ⟨0, h_n⟩) = ↑n := by omega
          have h4 : 2 * assignment ⟨0, h_n⟩ = ↑n - 2 := by linarith [h3]
          linarith [h_2x_ge, h4]
        exact this
      · have h_sym := horizontal_reflection_is_symmetry n
        unfold DomainSymmetry at h_sym
        have h_sol_reflected := h_sym assignment h_sol
        exact h_sol_reflected tc h_orig

/-- Result 3: General symmetry breaking constraint -/
theorem sb_constraint_is_symmetry_breaking (n : ℕ) (h_n : 0 < n) :
    symmetryBreakingConstraint (nqueens_csp n) (sb_constraint n h_n) := by
  unfold symmetryBreakingConstraint
  left
  exact sb_constraint_is_domain_symmetry_breaking n h_n

/-- Result 4: Equisatisfiability -/
theorem nqueens_equisatisfiability (n : ℕ) (h_n : 0 < n) :
    equisatisfiable (nqueens_csp n) (extended_nqueens_csp n h_n) := by
  apply domainSymmetryBreaking_equisatisfiability
  exact sb_constraint_is_domain_symmetry_breaking n h_n

-- ============================================================================
-- Solver translation
-- ============================================================================


def main : IO Unit := do
  let lb := 10
  let ub := 150
  let step := 10
  let count := ((ub - lb) / step) + 1
  let sizes := (List.range count).map (fun i => lb + i * step)

  IO.println s!"Generating N-Queens instances (BASE and +SBC) for n={lb} to n={ub}..."

  for n in sizes do
    if h_n : 0 < n then
      IO.println s!"  Generating n={n}..."

      let base_csp := nqueens_csp n
      let sbc_csp := extended_nqueens_csp n h_n

      -- Generate base instances
      saveToAuto base_csp s!"CSP/L2S/Proofs/mzn/nqueens/base_{n}" BackendType.MiniZinc
      saveToAuto base_csp s!"CSP/L2S/Proofs/smt2/nqueens/base_{n}" BackendType.SMTLIB

      -- Generate SBC instances
      saveToAuto sbc_csp s!"CSP/L2S/Proofs/mzn/nqueens/sbc_{n}" BackendType.MiniZinc
      saveToAuto sbc_csp s!"CSP/L2S/Proofs/smt2/nqueens/sbc_{n}" BackendType.SMTLIB
    else
      IO.println s!"  Skipping n={n}"

  IO.println s!"✓ Generated N-Queens instances for n={lb} to n={ub}"
