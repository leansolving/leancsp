import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Proofs.PatternBridges
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Card

open CSP.L2S

namespace Schur

/-!
## Schur Numbers Equivalent Formulations

### Formulation 1 (Compact / Color Model)
Variables: One per integer (n variables)
Domains: Colors {0, 1, ..., c-1}
Constraints: For each valid triple (i,j,k) with i+j+1=k, not all three have the same color

### Formulation 2 (Binary Matrix Model)
Variables: One per (integer, color) pair (n × c variables)
Domain: {0, 1} (binary)
Constraints:
- Each integer assigned exactly one color (one-hot encoding)
- For each triple and each color, at most 2 of the 3 can have that color

### π-Equivalence
We prove these formulations are π-equivalent via:
- Projection π: Matrix → Compact (extract color from one-hot encoding)
- Lifting λ: Compact → Matrix (construct one-hot encoding)

This is the `CSP/L2S` port of the `CSP/Int` proof: the satisfaction reasoning goes
through `patternHolds` and the `PatternBridges` `*_holds_iff` lemmas instead of the
dynamic-constraint checker.
-/

-- ============================================================================
-- Schur Triple Generation
-- ============================================================================

/-- Generate all Schur triples for {1, ..., n} (0-indexed).
    A triple (i, j, k) satisfies (i+1) + (j+1) = (k+1), i.e. k = i + j + 1,
    with i ≤ j and k < n. This includes x+x=2x triples for standard Schur numbers. -/
def schurTriples (n : ℕ) : List (Fin n × Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).filterMap fun j =>
      if _ : i.val ≤ j.val then
        let k_val := i.val + j.val + 1
        if h_k : k_val < n then
          some (i, j, ⟨k_val, h_k⟩)
        else none
      else none

-- ============================================================================
-- CSP Definitions
-- ============================================================================

section Definitions

variable (n colors : ℕ) (triples : List (Fin n × Fin n × Fin n))

-- Formulation 1: Compact Model

/-- Bounds: each integer has a color in {0, ..., colors-1} -/
def schur_bounds_1 : List (IntConstraint n) :=
  (List.finRange n).map (fun v => bound v 0 (colors - 1))

/-- Triple constraints: no monochromatic triple -/
def schur_constraints_1 : List (IntConstraint n) :=
  triples.map (fun ⟨i, j, k⟩ => schur_triple i j k)

/-- Compact model CSP -/
def schur_compact : IntCSP :=
  ⟨n, schur_bounds_1 n colors ++ schur_constraints_1 n triples⟩

-- Formulation 2: Binary Matrix Model

/-- Helper: index for cell (integer v, color d) in flattened matrix -/
def schurMatrixIndex (v : Fin n) (d : Fin colors) : Fin (n * colors) :=
  ⟨v.val * colors + d.val, by
    have h1 : v.val < n := v.isLt
    have h2 : d.val < colors := d.isLt
    calc v.val * colors + d.val
        < v.val * colors + colors := Nat.add_lt_add_left h2 _
      _ = (v.val + 1) * colors := by ring
      _ ≤ n * colors := Nat.mul_le_mul_right colors (Nat.succ_le_of_lt h1)⟩

/-- Helper: get all variables for an integer (row in matrix) -/
def integer_colors (v : Fin n) : _root_.Vector (VarType (n * colors)) colors :=
  _root_.Vector.ofFn (fun d => schurMatrixIndex n colors v d)

/-- Bounds: all matrix entries are binary {0, 1} -/
def schur_matrix_bounds_2 : List (IntConstraint (n * colors)) :=
  (List.finRange (n * colors)).map (fun idx => bound idx 0 1)

/-- One-hot constraint: each integer has exactly one color -/
def schur_one_hot_constraints_2 : List (IntConstraint (n * colors)) :=
  (List.finRange n).map (fun v => sum_eq (integer_colors n colors v) 1)

/-- Triple constraints: for each triple (i,j,k) and color d, at most 2 of 3 can have that color -/
def schur_triple_matrix_constraints_2 : List (IntConstraint (n * colors)) :=
  triples.flatMap fun ⟨i, j, k⟩ =>
    (List.finRange colors).map fun d =>
      let i_d := schurMatrixIndex n colors i d
      let j_d := schurMatrixIndex n colors j d
      let k_d := schurMatrixIndex n colors k d
      let scope := ⟨#[i_d, j_d, k_d], rfl⟩
      sum_le scope 2

/-- Binary matrix model CSP -/
def schur_expanded : IntCSP :=
  ⟨n * colors,
    schur_matrix_bounds_2 n colors ++
    schur_one_hot_constraints_2 n colors ++
    schur_triple_matrix_constraints_2 n colors triples⟩

end Definitions

-- ============================================================================
-- Projection and Lifting Functions
-- ============================================================================

/-- Projection π: Matrix → Compact
    For each integer v, find the unique color d where matrix[v,d] = 1 -/
def schur_π {n colors : ℕ} (x : IntAssignment (n * colors)) : IntAssignment n :=
  fun v : Fin n =>
    match (List.finRange colors).find? (fun d =>
      x (schurMatrixIndex n colors v d) = 1) with
    | some d => d.val
    | none => 0

/-- Lifting: Compact → Matrix
    Set matrix[v,d] = 1 iff assignment[v] = d -/
def schur_lift {n colors : ℕ} (h_colors : 0 < colors) (assignment : IntAssignment n) :
    IntAssignment (n * colors) :=
  fun idx : Fin (n * colors) =>
    let d : Fin colors := ⟨idx.val % colors, Nat.mod_lt idx.val h_colors⟩
    if assignment ⟨(idx.val / colors), by
      rw [Nat.div_lt_iff_lt_mul h_colors]
      exact idx.isLt⟩ = d.val then 1 else 0

-- ============================================================================
-- Auxiliary Lemmas
-- ============================================================================

section AuxiliaryLemmas

variable {n colors : ℕ} (h_colors : 0 < colors) (triples : List (Fin n × Fin n × Fin n))

/-- Matrix index division gives the integer -/
lemma schurMatrixIndex_div_eq (v : Fin n) (d : Fin colors) :
    (schurMatrixIndex n colors v d).val / colors = v.val := by
  unfold schurMatrixIndex
  simp only
  have h_d : d.val < colors := d.isLt
  have h_d_div_zero : d.val / colors = 0 := Nat.div_eq_zero_iff.mpr (Or.inr h_d)
  have h_colors_pos : 0 < colors := Fin.pos d
  rw [Nat.add_comm, Nat.mul_comm]
  rw [Nat.add_mul_div_left _ _ h_colors_pos]
  rw [h_d_div_zero]
  omega

/-- Matrix index modulo gives the color -/
lemma schurMatrixIndex_mod_eq (v : Fin n) (d : Fin colors) :
    (schurMatrixIndex n colors v d).val % colors = d.val := by
  unfold schurMatrixIndex
  simp only
  refine Nat.mul_add_mod_of_lt ?_
  exact d.isLt

/-- π∘lift is the identity (for valid colorings) -/
lemma schur_π_lift_inverse (assignment : IntAssignment n)
    (h_bounds : ∀ v : Fin n, 0 ≤ assignment v ∧ assignment v < colors) :
    schur_π (schur_lift h_colors assignment) = assignment := by
  funext v
  unfold schur_π
  have h_v := h_bounds v
  have h_toNat_eq : ((assignment v).toNat : ℤ) = assignment v := by
    exact Int.toNat_of_nonneg h_v.1
  let d_target : Fin colors := ⟨(assignment v).toNat, by
    exact (Int.toNat_lt h_v.1).mpr h_v.2⟩
  have h_find : (List.finRange colors).find? (fun d =>
      (schur_lift h_colors assignment) (schurMatrixIndex n colors v d) = 1) = some d_target := by
    have h_eq : List.finRange colors = List.ofFn id := rfl
    rw [h_eq]
    have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin colors) colors id
      (fun d => decide ((schur_lift h_colors assignment) (schurMatrixIndex n colors v d) = 1))
      d_target Function.injective_id
    simp only [id_eq] at h_lem
    rw [h_lem]
    constructor
    · simp only [decide_eq_true_eq]
      unfold schur_lift
      have h_mod := schurMatrixIndex_mod_eq v d_target
      have h_div := schurMatrixIndex_div_eq v d_target
      simp only [h_mod, ite_eq_left_iff]
      intro h_ne
      exfalso
      apply h_ne
      have : assignment v = (d_target.val : ℤ) := by
        simp [d_target, h_toNat_eq]
      have h_v_fin : ⟨(schurMatrixIndex n colors v d_target).val / colors, by
        rw [h_div]; exact v.isLt⟩ = v := by
        simp [h_div]
      rw [h_v_fin]
      exact this
    · intro d' h_d'_lt
      simp only [decide_eq_true_eq]
      unfold schur_lift
      have h_mod := schurMatrixIndex_mod_eq v d'
      have h_div := schurMatrixIndex_div_eq v d'
      simp only [h_mod]
      intro h_eq
      have h_target_eq : assignment v = (d_target.val : ℤ) := by
        simp [d_target, h_toNat_eq]
      have h_v_fin : ⟨(schurMatrixIndex n colors v d').val / colors, by
        rw [h_div]; exact v.isLt⟩ = v := by
        ext; simp [h_div]
      rw [h_v_fin] at h_eq
      have h_cond : assignment v = (d'.val : ℤ) := by
        by_contra h_ne
        simp [h_ne] at h_eq
      have : (d'.val : ℤ) = (d_target.val : ℤ) := by
        rw [← h_cond, h_target_eq]
      have : d'.val = d_target.val := by omega
      have : d' = d_target := Fin.ext this
      omega
  rw [h_find]
  simp
  rw [← h_toNat_eq]

/-- A matrix solution has exactly one color per integer -/
lemma schur_matrix_one_hot (x : IntAssignment (n * colors))
    (h_sol : IntCSP.isSolutionInt (schur_expanded n colors triples) x)
    (v : Fin n) :
    ∃! d : Fin colors, x (schurMatrixIndex n colors v d) = 1 := by
  have h_mem : sum_eq (integer_colors n colors v) 1 ∈
      (schur_expanded n colors triples).constraints := by
    unfold schur_expanded
    simp [schur_one_hot_constraints_2, List.finRange]
  have h_binary : ∀ d : Fin colors, x (schurMatrixIndex n colors v d) = 0 ∨ x (schurMatrixIndex n colors v d) = 1 := by
    intro d
    have h_bound_mem : bound (schurMatrixIndex n colors v d) 0 1 ∈
        (schur_expanded n colors triples).constraints := by
      unfold schur_expanded
      simp [schur_matrix_bounds_2, List.finRange]
    have h_bound_sat := (bound_holds_iff _ _ _ _).mp
      (h_sol (bound (schurMatrixIndex n colors v d) 0 1) h_bound_mem)
    have h_lb := h_bound_sat.1
    have h_ub := h_bound_sat.2
    by_cases h_eq_zero : x (schurMatrixIndex n colors v d) = 0
    · left; exact h_eq_zero
    · right
      have h_pos : 0 < x (schurMatrixIndex n colors v d) := by
        have : 0 ≠ x (schurMatrixIndex n colors v d) := fun a => h_eq_zero (id (Eq.symm a))
        exact Std.lt_of_le_of_ne h_lb this
      exact Eq.symm (Int.le_antisymm h_pos h_ub)
  have h_sum_matrixIndex : (List.ofFn fun d : Fin colors => x (schurMatrixIndex n colors v d)).sum = 1 := by
    have h_sat₀ : IntCSP.satisfiesConstraintInt (sum_eq (integer_colors n colors v) 1) x :=
      h_sol (sum_eq (integer_colors n colors v) 1) h_mem
    have h_sat := (sum_eq_holds_iff _ _ _).mp h_sat₀
    unfold integer_colors at h_sat
    simp only [_root_.Vector.toList_ofFn, List.map_ofFn] at h_sat
    simpa [Function.comp_def] using h_sat
  have h_exists : ∃ d : Fin colors, x (schurMatrixIndex n colors v d) = 1 := by
    by_contra h_none
    push Not at h_none
    have h_all_zero : ∀ d : Fin colors, x (schurMatrixIndex n colors v d) = 0 := by
      intro d
      cases h_binary d with
      | inl h => exact h
      | inr h => exact absurd h (h_none d)
    have h_sum_zero : (List.ofFn fun d : Fin colors => x (schurMatrixIndex n colors v d)).sum = 0 := by
      have : (fun d : Fin colors => x (schurMatrixIndex n colors v d)) = (fun _ => 0) := by
        funext d; exact h_all_zero d
      simp [this]
    rw [h_sum_zero] at h_sum_matrixIndex
    norm_num at h_sum_matrixIndex
  have h_unique : ∀ d₁ d₂ : Fin colors,
      x (schurMatrixIndex n colors v d₁) = 1 → x (schurMatrixIndex n colors v d₂) = 1 → d₁ = d₂ := by
    intro d₁ d₂ h₁ h₂
    by_contra h_ne
    have h_two : x (schurMatrixIndex n colors v d₁) + x (schurMatrixIndex n colors v d₂) = 2 := by
      rw [h₁, h₂]; norm_num
    have h_nonneg : ∀ d : Fin colors, 0 ≤ x (schurMatrixIndex n colors v d) := by
      intro d
      cases h_binary d with
      | inl h => rw [h]
      | inr h => rw [h]; norm_num
    have h_sum_ge_2 : (List.ofFn fun d : Fin colors => x (schurMatrixIndex n colors v d)).sum ≥ 2 := by
      have h_eq_finset : (List.ofFn fun d : Fin colors => x (schurMatrixIndex n colors v d)).sum =
                         (Finset.univ : Finset (Fin colors)).sum (fun d => x (schurMatrixIndex n colors v d)) := by
        have : (List.ofFn fun d : Fin colors => x (schurMatrixIndex n colors v d)) =
               List.map (fun d => x (schurMatrixIndex n colors v d)) (List.finRange colors) := by
          rw [List.ofFn_eq_map]
        rw [this]
        rw [← List.sum_toFinset _ (List.nodup_finRange colors)]
        congr 1
        exact List.toFinset_finRange colors
      rw [h_eq_finset]
      have h_decomp : (Finset.univ : Finset (Fin colors)).sum (fun d => x (schurMatrixIndex n colors v d)) =
                      x (schurMatrixIndex n colors v d₁) + x (schurMatrixIndex n colors v d₂) +
                      ((Finset.univ : Finset (Fin colors)) \ {d₁, d₂}).sum (fun d => x (schurMatrixIndex n colors v d)) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ {d₁, d₂})]
        have h_pair_sum : ({d₁, d₂} : Finset (Fin colors)).sum (fun d => x (schurMatrixIndex n colors v d)) =
                          x (schurMatrixIndex n colors v d₁) + x (schurMatrixIndex n colors v d₂) := by
          rw [Finset.sum_pair h_ne]
        rw [h_pair_sum, add_comm]
      rw [h_decomp]
      have h_rest_nonneg : 0 ≤ ((Finset.univ : Finset (Fin colors)) \ {d₁, d₂}).sum
          (fun d => x (schurMatrixIndex n colors v d)) := by
        apply Finset.sum_nonneg
        intros d _
        exact h_nonneg d
      linarith
    linarith
  cases h_exists with
  | intro d_wit h_wit =>
    use d_wit
    constructor
    · exact h_wit
    · intro d' h_d'
      exact (h_unique d_wit d' h_wit h_d').symm

/-- A compact solution has valid color bounds -/
lemma schur_compact_solution_bounds (assignment : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (schur_compact n colors triples) assignment)
    (v : Fin n) :
    0 ≤ assignment v ∧ assignment v < colors := by
  have h_mem : bound v 0 (colors - 1) ∈ (schur_compact n colors triples).constraints := by
    unfold schur_compact
    simp only [List.mem_append]
    left
    unfold schur_bounds_1
    simp only [List.mem_map, List.mem_finRange, true_and]
    use v
  have h_sat := (bound_holds_iff _ _ _ _).mp (h_sol (bound v 0 (colors - 1)) h_mem)
  constructor
  · exact h_sat.1
  · have h_ub : assignment v ≤ (colors : ℤ) - 1 := h_sat.2
    linarith

end AuxiliaryLemmas

-- ============================================================================
-- Main Theorems
-- ============================================================================

section MainTheorems

variable {n colors : ℕ} (h_colors : 0 < colors) (triples : List (Fin n × Fin n × Fin n))

/-- Forward direction: matrix solution projects to compact solution -/
theorem schur_forward (sol₂ : IntAssignment (n * colors))
    (h_sol₂ : IntCSP.isSolutionInt (schur_expanded n colors triples) sol₂) :
    IntCSP.isSolutionInt (schur_compact n colors triples) (schur_π sol₂) := by
  unfold IntCSP.isSolutionInt
  intro c h_c
  unfold schur_compact at h_c
  simp only [List.mem_append] at h_c
  rcases h_c with h_bounds | h_triples
  · -- Bounds case: π gives a value in [0, colors-1]
    obtain ⟨v, ⟨_, h_eq⟩⟩ := (List.mem_map.mp h_bounds)
    subst h_eq
    show IntCSP.satisfiesConstraintInt (bound v 0 ((colors : ℤ) - 1)) (schur_π sol₂)
    rw [bound_holds_iff]
    unfold schur_π
    have h_one_hot : ∃! d : Fin colors, sol₂ (schurMatrixIndex n colors v d) = 1 := by
      apply schur_matrix_one_hot
      exact h_sol₂
    have ⟨d_wit, h_wit, _⟩ := h_one_hot
    constructor
    · split
      · exact Int.natCast_nonneg _
      · omega
    · split
      next d h_some =>
        have hd : (d.val : ℤ) < (colors : ℤ) := by exact_mod_cast d.isLt
        exact Int.le_sub_one_of_lt hd
      next h_none =>
        have hc : (0 : ℤ) < (colors : ℤ) := by exact_mod_cast Fin.pos d_wit
        exact Int.sub_nonneg_of_le hc
  · -- Triple constraints: schur_triple preserved
    obtain ⟨⟨i, j, k⟩, ⟨h_triple_mem, h_eq⟩⟩ := (List.mem_map.mp h_triples)
    subst h_eq
    show IntCSP.satisfiesConstraintInt (schur_triple i j k) (schur_π sol₂)
    rw [schur_triple_holds_iff]
    -- We need to show: not all three π-values are equal
    have h_one_hot_i : ∃! d : Fin colors, sol₂ (schurMatrixIndex n colors i d) = 1 :=
      schur_matrix_one_hot triples sol₂ h_sol₂ i
    have h_one_hot_j : ∃! d : Fin colors, sol₂ (schurMatrixIndex n colors j d) = 1 :=
      schur_matrix_one_hot triples sol₂ h_sol₂ j
    have h_one_hot_k : ∃! d : Fin colors, sol₂ (schurMatrixIndex n colors k d) = 1 :=
      schur_matrix_one_hot triples sol₂ h_sol₂ k
    obtain ⟨d_i, h_i_wit, h_i_uniq⟩ := h_one_hot_i
    obtain ⟨d_j, h_j_wit, h_j_uniq⟩ := h_one_hot_j
    obtain ⟨d_k, h_k_wit, h_k_uniq⟩ := h_one_hot_k
    -- Show that find? returns the witness for each
    have h_find_i : (List.finRange colors).find? (fun d => sol₂ (schurMatrixIndex n colors i d) = 1) = some d_i := by
      have h_eq_list : List.finRange colors = List.ofFn id := rfl
      rw [h_eq_list]
      have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin colors) colors id
        (fun d => decide (sol₂ (schurMatrixIndex n colors i d) = 1))
        d_i Function.injective_id
      simp only [id_eq] at h_lem
      rw [h_lem]
      constructor
      · simp only [decide_eq_true_eq]; exact h_i_wit
      · intro d' h_lt; simp only [decide_eq_true_eq]; intro h_contra
        have : d' = d_i := h_i_uniq d' h_contra
        rw [this] at h_lt; exact Nat.lt_irrefl d_i.val h_lt
    have h_find_j : (List.finRange colors).find? (fun d => sol₂ (schurMatrixIndex n colors j d) = 1) = some d_j := by
      have h_eq_list : List.finRange colors = List.ofFn id := rfl
      rw [h_eq_list]
      have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin colors) colors id
        (fun d => decide (sol₂ (schurMatrixIndex n colors j d) = 1))
        d_j Function.injective_id
      simp only [id_eq] at h_lem
      rw [h_lem]
      constructor
      · simp only [decide_eq_true_eq]; exact h_j_wit
      · intro d' h_lt; simp only [decide_eq_true_eq]; intro h_contra
        have : d' = d_j := h_j_uniq d' h_contra
        rw [this] at h_lt; exact Nat.lt_irrefl d_j.val h_lt
    have h_find_k : (List.finRange colors).find? (fun d => sol₂ (schurMatrixIndex n colors k d) = 1) = some d_k := by
      have h_eq_list : List.finRange colors = List.ofFn id := rfl
      rw [h_eq_list]
      have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin colors) colors id
        (fun d => decide (sol₂ (schurMatrixIndex n colors k d) = 1))
        d_k Function.injective_id
      simp only [id_eq] at h_lem
      rw [h_lem]
      constructor
      · simp only [decide_eq_true_eq]; exact h_k_wit
      · intro d' h_lt; simp only [decide_eq_true_eq]; intro h_contra
        have : d' = d_k := h_k_uniq d' h_contra
        rw [this] at h_lt; exact Nat.lt_irrefl d_k.val h_lt
    -- Suppose they're all equal. Then d_i = d_j = d_k, contradicting sum_le 2
    by_contra h_neg
    push Not at h_neg
    obtain ⟨h_ij, h_ik, _⟩ := h_neg
    unfold schur_π at h_ij h_ik
    simp only [h_find_i, h_find_j, h_find_k] at h_ij h_ik
    have h_d_ij : d_i = d_j := by
      apply Fin.ext; exact Nat.cast_injective h_ij
    have h_d_ik : d_i = d_k := by
      apply Fin.ext; exact Nat.cast_injective h_ik
    -- All three have color d_i, so sum = 3 > 2
    have h_constr : sum_le ⟨#[schurMatrixIndex n colors i d_i, schurMatrixIndex n colors j d_i, schurMatrixIndex n colors k d_i], rfl⟩ 2 ∈
        (schur_expanded n colors triples).constraints := by
      unfold schur_expanded schur_triple_matrix_constraints_2
      simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and, Prod.exists]
      right
      use i, j, k, h_triple_mem, d_i
    have h_sat := (sum_le_holds_iff _ _ _).mp (h_sol₂ _ h_constr)
    change ([sol₂ (schurMatrixIndex n colors i d_i), sol₂ (schurMatrixIndex n colors j d_i),
        sol₂ (schurMatrixIndex n colors k d_i)]).sum ≤ 2 at h_sat
    rw [List.sum_cons, List.sum_cons, List.sum_cons, List.sum_nil, add_zero] at h_sat
    rw [h_i_wit] at h_sat
    have h_j_eq : sol₂ (schurMatrixIndex n colors j d_i) = 1 := by rw [h_d_ij]; exact h_j_wit
    have h_k_eq : sol₂ (schurMatrixIndex n colors k d_i) = 1 := by rw [h_d_ik]; exact h_k_wit
    rw [h_j_eq, h_k_eq] at h_sat
    norm_num at h_sat

/-- Backward direction: compact solution lifts to matrix solution -/
theorem schur_backward (h_pos : 0 < colors) (sol₁ : IntAssignment n)
    (h_sol₁ : IntCSP.isSolutionInt (schur_compact n colors triples) sol₁) :
    ∃ sol₂ : IntAssignment (n * colors),
      IntCSP.isSolutionInt (schur_expanded n colors triples) sol₂ ∧
      schur_π sol₂ = sol₁ := by
  let sol₂ := schur_lift h_pos sol₁
  use sol₂
  constructor
  · unfold IntCSP.isSolutionInt
    intro c h_c
    unfold schur_expanded at h_c
    unfold schur_matrix_bounds_2 schur_one_hot_constraints_2 schur_triple_matrix_constraints_2 at h_c
    simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_flatMap, true_and, Prod.exists] at h_c
    rcases h_c with (⟨idx, h_eq⟩ | ⟨v, h_eq⟩) | ⟨i, j, k, h_triple_mem, color, h_eq⟩
    · -- Binary bounds
      subst h_eq
      show IntCSP.satisfiesConstraintInt (bound idx 0 1) sol₂
      rw [bound_holds_iff]
      show 0 ≤ sol₂ idx ∧ sol₂ idx ≤ 1
      unfold sol₂ schur_lift
      simp only
      split_ifs
      · constructor <;> norm_num
      · constructor <;> norm_num
    · -- One-hot constraints
      subst h_eq
      show IntCSP.satisfiesConstraintInt (sum_eq (integer_colors n colors v) 1) sol₂
      rw [sum_eq_holds_iff]
      unfold integer_colors
      simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
      have h_v_bounds := schur_compact_solution_bounds triples sol₁ h_sol₁ v
      have h_v_nonneg : 0 ≤ sol₁ v := h_v_bounds.1
      have h_v_lt : sol₁ v < colors := h_v_bounds.2
      have h_toNat_eq : ((sol₁ v).toNat : ℤ) = sol₁ v := Int.toNat_of_nonneg h_v_nonneg
      let d_target : Fin colors := ⟨(sol₁ v).toNat, by
        exact (Int.toNat_lt h_v_nonneg).mpr h_v_lt⟩
      show (List.ofFn fun d : Fin colors => sol₂ (schurMatrixIndex n colors v d)).sum = 1
      have h_term : ∀ d : Fin colors, sol₂ (schurMatrixIndex n colors v d) =
          if d.val = (sol₁ v).toNat then (1 : ℤ) else 0 := by
        intro d
        unfold sol₂ schur_lift
        have h_div : (schurMatrixIndex n colors v d).val / colors = v.val := schurMatrixIndex_div_eq v d
        have h_mod : (schurMatrixIndex n colors v d).val % colors = d.val := schurMatrixIndex_mod_eq v d
        simp only [h_mod]
        have h_vertex_eq : (⟨(schurMatrixIndex n colors v d).val / colors, by
          rw [Nat.div_lt_iff_lt_mul h_pos]
          exact (schurMatrixIndex n colors v d).isLt⟩ : Fin n) = v := by
          ext; exact h_div
        rw [h_vertex_eq]
        have h_cast_eq : sol₁ v = ↑d.val ↔ d.val = (sol₁ v).toNat := by
          constructor
          · intro h
            have : Int.toNat (sol₁ v) = Int.toNat (↑d.val : ℤ) := by rw [h]
            rw [this, Int.toNat_natCast]
          · intro h
            calc sol₁ v = ↑(Int.toNat (sol₁ v)) := h_toNat_eq.symm
                 _      = ↑d.val := by rw [h]
        by_cases h : sol₁ v = ↑d.val
        · rw [if_pos h, if_pos (h_cast_eq.mp h)]
        · rw [if_neg h, if_neg (mt h_cast_eq.mpr h)]
      simp only [h_term]
      have h_d_target_val : d_target.val = (sol₁ v).toNat := rfl
      have h_d_target_unique : ∀ d : Fin colors, d.val = (sol₁ v).toNat → d = d_target := by
        intro d h_eq; ext; rw [h_eq, h_d_target_val]
      trans ((List.ofFn fun d : Fin colors => if d = d_target then (1 : ℤ) else 0).sum)
      · congr 1
        have h_fn_eq : (fun d : Fin colors => if d.val = (sol₁ v).toNat then (1 : ℤ) else 0) =
                       (fun d : Fin colors => if d = d_target then (1 : ℤ) else 0) := by
          funext d
          by_cases h : d.val = (sol₁ v).toNat
          · rw [if_pos h, if_pos (h_d_target_unique d h)]
          · rw [if_neg h]
            have : d ≠ d_target := fun h_eq => h (by rw [h_eq, h_d_target_val])
            rw [if_neg this]
        rw [h_fn_eq]
      · have h_eq_finset : (List.ofFn fun d : Fin colors => if d = d_target then (1 : ℤ) else 0).sum =
                           ∑ d : Fin colors, if d = d_target then (1 : ℤ) else 0 := by
          rw [List.sum_ofFn]
        rw [h_eq_finset]
        rw [Finset.sum_eq_single d_target]
        · simp
        · intro b _ h_ne; simp [h_ne]
        · intro h_mem; exfalso; exact h_mem (Finset.mem_univ d_target)
    · -- Triple sum_le constraints
      subst h_eq
      show IntCSP.satisfiesConstraintInt (sum_le ⟨#[schurMatrixIndex n colors i color, schurMatrixIndex n colors j color, schurMatrixIndex n colors k color], rfl⟩ 2) sol₂
      rw [sum_le_holds_iff]
      change ([sol₂ (schurMatrixIndex n colors i color),
             sol₂ (schurMatrixIndex n colors j color),
             sol₂ (schurMatrixIndex n colors k color)]).sum ≤ 2
      rw [List.sum_cons, List.sum_cons, List.sum_cons, List.sum_nil, add_zero]
      unfold sol₂ schur_lift
      simp only
      have h_i_div : (schurMatrixIndex n colors i color).val / colors = i.val := schurMatrixIndex_div_eq i color
      have h_i_mod : (schurMatrixIndex n colors i color).val % colors = color.val := schurMatrixIndex_mod_eq i color
      have h_j_div : (schurMatrixIndex n colors j color).val / colors = j.val := schurMatrixIndex_div_eq j color
      have h_j_mod : (schurMatrixIndex n colors j color).val % colors = color.val := schurMatrixIndex_mod_eq j color
      have h_k_div : (schurMatrixIndex n colors k color).val / colors = k.val := schurMatrixIndex_div_eq k color
      have h_k_mod : (schurMatrixIndex n colors k color).val % colors = color.val := schurMatrixIndex_mod_eq k color
      have h_i_fin : (⟨(schurMatrixIndex n colors i color).val / colors, by
        rw [h_i_div]; exact i.isLt⟩ : Fin n) = i := by ext; exact h_i_div
      have h_j_fin : (⟨(schurMatrixIndex n colors j color).val / colors, by
        rw [h_j_div]; exact j.isLt⟩ : Fin n) = j := by ext; exact h_j_div
      have h_k_fin : (⟨(schurMatrixIndex n colors k color).val / colors, by
        rw [h_k_div]; exact k.isLt⟩ : Fin n) = k := by ext; exact h_k_div
      simp only [h_i_fin, h_j_fin, h_k_fin, h_i_mod, h_j_mod, h_k_mod]
      -- At most 2 of the 3 can be 1 because schur_triple says not all equal
      split_ifs with h_i h_j h_k
      · -- All three equal to color: contradicts schur_triple constraint
        exfalso
        have h_triple_constr : schur_triple i j k ∈ (schur_compact n colors triples).constraints := by
          unfold schur_compact schur_constraints_1
          simp only [List.mem_append, List.mem_map]
          right
          use (i, j, k)
        have h_sat_triple := (schur_triple_holds_iff _ _ _ _).mp
          (h_sol₁ (schur_triple i j k) h_triple_constr)
        rcases h_sat_triple with h_ne_ij | h_ne_ik | h_ne_jk
        · exact h_ne_ij (by rw [h_i, h_j])
        · exact h_ne_ik (by rw [h_i, h_k])
        · exact h_ne_jk (by rw [h_j, h_k])
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  · have h_bounds : ∀ v : Fin n, 0 ≤ sol₁ v ∧ sol₁ v < colors := by
      intro v; apply schur_compact_solution_bounds; exact h_sol₁
    exact schur_π_lift_inverse h_pos sol₁ h_bounds

/-- Injectivity: different matrix solutions with same projection are equal -/
theorem schur_injective (h_pos : 0 < colors) (sol₂ sol₂' : IntAssignment (n * colors))
    (h_sol₂ : IntCSP.isSolutionInt (schur_expanded n colors triples) sol₂)
    (h_sol₂' : IntCSP.isSolutionInt (schur_expanded n colors triples) sol₂')
    (h_proj_eq : schur_π sol₂ = schur_π sol₂') :
    sol₂ = sol₂' := by
  funext idx
  let v : Fin n := ⟨idx.val / colors, by
    rw [Nat.div_lt_iff_lt_mul h_pos]; exact idx.isLt⟩
  let d : Fin colors := ⟨idx.val % colors, Nat.mod_lt idx.val h_pos⟩
  have h_idx_eq : idx = schurMatrixIndex n colors v d := by
    apply Fin.ext
    unfold schurMatrixIndex
    simp only
    show idx.val = v.val * colors + d.val
    have h_div_mod : idx.val = colors * (idx.val / colors) + idx.val % colors :=
      (Nat.div_add_mod idx.val colors).symm
    calc idx.val = colors * (idx.val / colors) + idx.val % colors := h_div_mod
         _ = (idx.val / colors) * colors + idx.val % colors := by rw [Nat.mul_comm]
         _ = v.val * colors + d.val := by rfl
  have h_one_hot₂ : ∃! d : Fin colors, sol₂ (schurMatrixIndex n colors v d) = 1 :=
    schur_matrix_one_hot triples sol₂ h_sol₂ v
  have h_one_hot₂' : ∃! d : Fin colors, sol₂' (schurMatrixIndex n colors v d) = 1 :=
    schur_matrix_one_hot triples sol₂' h_sol₂' v
  obtain ⟨d₂, h₂_wit, h₂_uniq⟩ := h_one_hot₂
  obtain ⟨d₂', h₂'_wit, h₂'_uniq⟩ := h_one_hot₂'
  have h_proj_v : schur_π sol₂ v = schur_π sol₂' v := congrFun h_proj_eq v
  have h_π₂ : schur_π sol₂ v = ↑(d₂.val) := by
    unfold schur_π
    have h_find : List.find? (fun d => sol₂ (schurMatrixIndex n colors v d) = 1) (List.finRange colors) = some d₂ := by
      rw [List.finRange]
      have h_id : (fun i : Fin colors => i) = id := rfl
      rw [h_id]
      show List.find? (fun d => sol₂ (schurMatrixIndex n colors v d) = 1) (List.ofFn id) = some (id d₂)
      rw [List.find?_ofFn_eq_some_of_injective (f := id) (p := fun d => sol₂ (schurMatrixIndex n colors v d) = 1)]
      constructor
      · simp [h₂_wit]
      · intro j h_lt; simp; intro h_contra
        have : j = d₂ := h₂_uniq j h_contra
        rw [this] at h_lt; exact Nat.lt_irrefl d₂.val h_lt
      · exact fun _ _ => id
    simp [h_find]
  have h_π₂' : schur_π sol₂' v = ↑(d₂'.val) := by
    unfold schur_π
    have h_find' : List.find? (fun d => sol₂' (schurMatrixIndex n colors v d) = 1) (List.finRange colors) = some d₂' := by
      rw [List.finRange]
      have h_id : (fun i : Fin colors => i) = id := rfl
      rw [h_id]
      show List.find? (fun d => sol₂' (schurMatrixIndex n colors v d) = 1) (List.ofFn id) = some (id d₂')
      rw [List.find?_ofFn_eq_some_of_injective (f := id) (p := fun d => sol₂' (schurMatrixIndex n colors v d) = 1)]
      constructor
      · simp [h₂'_wit]
      · intro j h_lt; simp; intro h_contra
        have : j = d₂' := h₂'_uniq j h_contra
        rw [this] at h_lt; exact Nat.lt_irrefl d₂'.val h_lt
      · exact fun _ _ => id
    simp [h_find']
  have h_d_eq : d₂ = d₂' := by
    apply Fin.ext
    have : (d₂.val : ℤ) = (d₂'.val : ℤ) := by rw [← h_π₂, ← h_π₂', h_proj_v]
    exact Nat.cast_injective this
  rw [h_idx_eq]
  by_cases h_case : d = d₂
  · calc sol₂ (schurMatrixIndex n colors v d)
        = sol₂ (schurMatrixIndex n colors v d₂) := by rw [h_case]
      _ = 1 := h₂_wit
      _ = sol₂' (schurMatrixIndex n colors v d₂') := h₂'_wit.symm
      _ = sol₂' (schurMatrixIndex n colors v d) := by rw [← h_d_eq, ← h_case]
  · have h₂_zero : sol₂ (schurMatrixIndex n colors v d) = 0 := by
      have h_bound_mem : bound (schurMatrixIndex n colors v d) 0 1 ∈
          (schur_expanded n colors triples).constraints := by
        unfold schur_expanded; simp [schur_matrix_bounds_2, List.finRange]
      have h_bound_sat := (bound_holds_iff _ _ _ _).mp
        (h_sol₂ (bound (schurMatrixIndex n colors v d) 0 1) h_bound_mem)
      by_cases h_val : sol₂ (schurMatrixIndex n colors v d) = 1
      · exact absurd (h₂_uniq d h_val) h_case
      · have h_lb := h_bound_sat.1
        have h_ub := h_bound_sat.2
        have : sol₂ (schurMatrixIndex n colors v d) < 1 :=
          Int.lt_iff_le_and_ne.mpr ⟨h_ub, h_val⟩
        have : sol₂ (schurMatrixIndex n colors v d) ≤ 0 :=
          Int.le_iff_lt_add_one.mpr this
        exact Int.le_antisymm this h_lb
    have h₂'_zero : sol₂' (schurMatrixIndex n colors v d) = 0 := by
      have h_bound_mem : bound (schurMatrixIndex n colors v d) 0 1 ∈
          (schur_expanded n colors triples).constraints := by
        unfold schur_expanded; simp [schur_matrix_bounds_2, List.finRange]
      have h_bound_sat := (bound_holds_iff _ _ _ _).mp
        (h_sol₂' (bound (schurMatrixIndex n colors v d) 0 1) h_bound_mem)
      by_cases h_val : sol₂' (schurMatrixIndex n colors v d) = 1
      · have h_eq_d₂' : d = d₂' := h₂'_uniq d h_val
        have : d = d₂ := by rw [h_eq_d₂', h_d_eq.symm]
        exact absurd this h_case
      · have h_lb := h_bound_sat.1
        have h_ub := h_bound_sat.2
        have : sol₂' (schurMatrixIndex n colors v d) < 1 :=
          Int.lt_iff_le_and_ne.mpr ⟨h_ub, h_val⟩
        have : sol₂' (schurMatrixIndex n colors v d) ≤ 0 :=
          Int.le_iff_lt_add_one.mpr this
        exact Int.le_antisymm this h_lb
    rw [h₂_zero, h₂'_zero]

end MainTheorems

-- ============================================================================
-- π-Equivalence Theorem
-- ============================================================================

theorem schur_pi_equivalent (n colors : ℕ) (h_colors : 0 < colors)
    (triples : List (Fin n × Fin n × Fin n)) :
    piEquivalent
      (schur_compact n colors triples)
      (schur_expanded n colors triples)
      (@schur_π n colors) := by
  constructor
  · exact schur_forward triples
  constructor
  · exact schur_backward triples h_colors
  · exact schur_injective triples h_colors

/-- Derived: Full equivalence -/
theorem schur_equivalent (n colors : ℕ) (h_colors : 0 < colors)
    (triples : List (Fin n × Fin n × Fin n)) :
    equivalent
      (schur_expanded n colors triples)
      (schur_compact n colors triples) := by
  apply piEquivalent_implies_equivalent
  exact schur_pi_equivalent n colors h_colors triples

/-- Derived: Equisatisfiability -/
theorem schur_equisatisfiable (n colors : ℕ) (h_colors : 0 < colors)
    (triples : List (Fin n × Fin n × Fin n)) :
    equisatisfiable
      (schur_compact n colors triples)
      (schur_expanded n colors triples) := by
  apply piEquivalent_implies_equisatisfiable
  exact schur_pi_equivalent n colors h_colors triples

-- ============================================================================
-- Instantiated Versions (triples computed from n)
-- ============================================================================

/-- Schur compact CSP with triples computed from n -/
def schur (n colors : ℕ) : IntCSP :=
  schur_compact n colors (schurTriples n)

/-- Schur expanded CSP with triples computed from n -/
def schur_matrix (n colors : ℕ) : IntCSP :=
  schur_expanded n colors (schurTriples n)

theorem schur_pi_equivalent' (n colors : ℕ) (h_colors : 0 < colors) :
    piEquivalent (schur n colors) (schur_matrix n colors) (@schur_π n colors) :=
  schur_pi_equivalent n colors h_colors (schurTriples n)

theorem schur_equivalent' (n colors : ℕ) (h_colors : 0 < colors) :
    equivalent (schur_matrix n colors) (schur n colors) :=
  schur_equivalent n colors h_colors (schurTriples n)

theorem schur_equisatisfiable' (n colors : ℕ) (h_colors : 0 < colors) :
    equisatisfiable (schur n colors) (schur_matrix n colors) :=
  schur_equisatisfiable n colors h_colors (schurTriples n)

end Schur
