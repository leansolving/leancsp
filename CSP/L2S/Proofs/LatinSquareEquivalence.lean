import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Proofs.LatinSquareSB
import CSP.L2S.Proofs.PatternBridges
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Card
import Aesop

open CSP.L2S

namespace LatinSquare

/-!
## Latin Square π-Equivalence: Value-Based ↔ One-Hot Binary

### Formulation 1 (Value-Based, Compact)
Variables: n² (one per cell), Domain: {0, ..., n-1}
Constraints: bounds, row alldifferent, column alldifferent
This is `latin_square_csp n` from LatinSquareSB.lean.

### Formulation 2 (One-Hot Binary, Expanded)
Variables: n³ (one per (cell, value) triple), Domain: {0, 1}
Constraints: binary bounds, cell one-hot (sum=1), row-value uniqueness (sum=1),
             column-value uniqueness (sum=1)

### π-Equivalence
We prove these formulations are π-equivalent via:
- Projection π: Expanded → Compact (find unique 1 per cell group)
- Lifting lift: Compact → Expanded (one-hot encode each cell value)

This is the `CSP/L2S` port of the `CSP/Int` proof: the satisfaction reasoning goes
through `patternHolds` and the `PatternBridges` `*_holds_iff` lemmas instead of the
dynamic-constraint checker.
-/

/-- Local port helper: a vector scope mapped through an assignment equals the
    `List.ofFn`/`Vector.get` form some of the index arithmetic is phrased in. -/
private lemma ls_toList_map_get {N k : ℕ} (vec : _root_.Vector (VarType N) k)
    (a : IntAssignment N) :
    vec.toList.map a = List.ofFn fun j => a (vec.get j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [_root_.Vector.get]

-- ============================================================================
-- Expanded CSP Definitions (Formulation 2)
-- ============================================================================

section Definitions

variable (n : ℕ)

/-- Cell index in expanded CSP: cell c ∈ Fin (n*n), value v ∈ Fin n → Fin (n*n*n) -/
def ls_cellIndex (c : Fin (n*n)) (v : Fin n) : Fin (n*n*n) :=
  ⟨c.val * n + v.val, by
    have h1 : c.val < n * n := c.isLt
    have h2 : v.val < n := v.isLt
    calc c.val * n + v.val
        < c.val * n + n := Nat.add_lt_add_left h2 _
      _ = (c.val + 1) * n := by ring
      _ ≤ n * n * n := by
          have : c.val + 1 ≤ n * n := Nat.succ_le_of_lt h1
          exact Nat.mul_le_mul_right n this⟩

/-- All n value-variables for a given cell -/
def ls_cell_vars (c : Fin (n*n)) : _root_.Vector (Fin (n*n*n)) n :=
  _root_.Vector.ofFn (fun v => ls_cellIndex n c v)

/-- Row-value variables: for row i and value v, the n cells in that row with that value.
    Variable index is (i*n+j)*n + v for j = 0..n-1 -/
def ls_row_value_vars (i : Fin n) (v : Fin n) :
    _root_.Vector (Fin (n*n*n)) n :=
  _root_.Vector.ofFn (fun j : Fin n =>
    ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v)

/-- Column-value variables: for col j and value v, the n cells in that column with that value.
    Variable index is (i*n+j)*n + v for i = 0..n-1 -/
def ls_col_value_vars (j : Fin n) (v : Fin n) :
    _root_.Vector (Fin (n*n*n)) n :=
  _root_.Vector.ofFn (fun i : Fin n =>
    ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v)

/-- Binary bounds: 0 ≤ x[idx] ≤ 1 for all n³ variables -/
def ls_binary_bounds : List (IntConstraint (n*n*n)) :=
  (List.finRange (n*n*n)).map (fun idx => bound idx 0 1)

/-- Cell one-hot: for each cell c, Σ_v x[c*n + v] = 1 -/
def ls_cell_one_hot : List (IntConstraint (n*n*n)) :=
  (List.finRange (n*n)).map (fun c => sum_eq (ls_cell_vars n c) 1)

/-- Row-value uniqueness: for each (row i, value v), Σ_j x[(i*n+j)*n + v] = 1 -/
def ls_row_value_constraints : List (IntConstraint (n*n*n)) :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).map fun v =>
      sum_eq (ls_row_value_vars n i v) 1

/-- Column-value uniqueness: for each (col j, value v), Σ_i x[(i*n+j)*n + v] = 1 -/
def ls_col_value_constraints : List (IntConstraint (n*n*n)) :=
  (List.finRange n).flatMap fun j =>
    (List.finRange n).map fun v =>
      sum_eq (ls_col_value_vars n j v) 1

/-- Full expanded CSP -/
def latin_square_matrix : IntCSP :=
  ⟨n*n*n,
    ls_binary_bounds n ++
    ls_cell_one_hot n ++
    ls_row_value_constraints n ++
    ls_col_value_constraints n⟩

end Definitions

-- ============================================================================
-- Projection and Lifting Functions
-- ============================================================================

/-- π: expanded → compact (find unique 1 per cell group) -/
def ls_π {n : ℕ} (x : IntAssignment (n*n*n)) : IntAssignment (n*n) :=
  fun c : Fin (n*n) =>
    match (List.finRange n).find? (fun v =>
      x (ls_cellIndex n c v) = 1) with
    | some v => v.val
    | none => 0

/-- lift: compact → expanded (one-hot encode each cell value) -/
def ls_lift {n : ℕ} (h_n : 0 < n) (a : IntAssignment (n*n)) :
    IntAssignment (n*n*n) :=
  fun idx : Fin (n*n*n) =>
    let c : Fin (n*n) := ⟨idx.val / n, by
      rw [Nat.div_lt_iff_lt_mul h_n]
      exact idx.isLt⟩
    let v : Fin n := ⟨idx.val % n, Nat.mod_lt idx.val h_n⟩
    if a c = v.val then 1 else 0

-- ============================================================================
-- Arithmetic Lemmas
-- ============================================================================

section ArithmeticLemmas

variable {n : ℕ} (h_n : 0 < n)

/-- Cell index division gives the cell -/
lemma ls_cellIndex_div (c : Fin (n*n)) (v : Fin n) :
    (ls_cellIndex n c v).val / n = c.val := by
  unfold ls_cellIndex
  simp only
  have h_pos : 0 < n := by have := v.isLt; omega
  rw [show c.val * n + v.val = v.val + c.val * n from by omega]
  rw [Nat.add_mul_div_right _ _ h_pos, Nat.div_eq_of_lt v.isLt, Nat.zero_add]

/-- Cell index modulo gives the value -/
lemma ls_cellIndex_mod (c : Fin (n*n)) (v : Fin n) :
    (ls_cellIndex n c v).val % n = v.val := by
  unfold ls_cellIndex
  simp only
  exact Nat.mul_add_mod_of_lt v.isLt

/-- Cell coordinate bound: i * n + j < n * n for i, j : Fin n -/
private lemma ls_cell_lt {n : ℕ} (i j : Fin n) : i.val * n + j.val < n * n := by
  have hi := i.isLt; have hj := j.isLt
  have : 0 < n := by omega
  nlinarith [Nat.mul_lt_mul_of_pos_right hi ‹0 < n›]

end ArithmeticLemmas

-- ============================================================================
-- Generic Infrastructure (ported from GraphColoringEquivalence)
-- ============================================================================

section GenericInfrastructure

variable {n : ℕ} (h_n : 0 < n)

/-- A matrix solution has binary values -/
lemma ls_binary_values (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (idx : Fin (n*n*n)) :
    x idx = 0 ∨ x idx = 1 := by
  have h_bound_mem : bound idx 0 1 ∈ (latin_square_matrix n).constraints := by
    unfold latin_square_matrix
    simp [ls_binary_bounds, List.finRange]
  have h_bound_sat := (bound_holds_iff _ _ _ _).mp (h_sol (bound idx 0 1) h_bound_mem)
  have h_lb := h_bound_sat.1
  have h_ub := h_bound_sat.2
  by_cases h_eq_zero : x idx = 0
  · left; exact h_eq_zero
  · right
    have h_pos : 0 < x idx := by
      exact Std.lt_of_le_of_ne h_lb (fun a => h_eq_zero (id (Eq.symm a)))
    exact Eq.symm (Int.le_antisymm h_pos h_ub)

/-- Cell one-hot sum from solution -/
lemma ls_cell_sum (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (c : Fin (n*n)) :
    (List.ofFn fun v : Fin n => x (ls_cellIndex n c v)).sum = 1 := by
  have h_mem : sum_eq (ls_cell_vars n c) 1 ∈ (latin_square_matrix n).constraints := by
    unfold latin_square_matrix
    simp [ls_cell_one_hot, List.finRange]
  have h_sat := (sum_eq_holds_iff _ _ _).mp (h_sol (sum_eq (ls_cell_vars n c) 1) h_mem)
  simp only [ls_cell_vars, latin_square_matrix, CSP.L2S.VarType] at h_sat
  rw [_root_.Vector.toList_ofFn] at h_sat
  simpa [Function.comp_def, List.map_ofFn] using h_sat

/-- Exactly one value is 1 per cell (one-hot) -/
lemma ls_one_hot_exactly_one (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (c : Fin (n*n)) :
    ∃! v : Fin n, x (ls_cellIndex n c v) = 1 := by
  have h_binary := fun idx => ls_binary_values x h_sol idx
  have h_sum := ls_cell_sum x h_sol c
  have h_exists : ∃ v : Fin n, x (ls_cellIndex n c v) = 1 := by
    by_contra h_none
    push Not at h_none
    have h_all_zero : ∀ v : Fin n, x (ls_cellIndex n c v) = 0 := by
      intro v
      cases h_binary (ls_cellIndex n c v) with
      | inl h => exact h
      | inr h => exact absurd h (h_none v)
    have : (List.ofFn fun v : Fin n => x (ls_cellIndex n c v)).sum = 0 := by
      have : (fun v : Fin n => x (ls_cellIndex n c v)) = (fun _ => 0) := by
        funext v; exact h_all_zero v
      simp [this]
    linarith
  have h_unique : ∀ v₁ v₂ : Fin n,
      x (ls_cellIndex n c v₁) = 1 → x (ls_cellIndex n c v₂) = 1 → v₁ = v₂ := by
    intro v₁ v₂ h₁ h₂
    by_contra h_ne
    have h_nonneg : ∀ v : Fin n, 0 ≤ x (ls_cellIndex n c v) := by
      intro v
      cases h_binary (ls_cellIndex n c v) with
      | inl h => rw [h]
      | inr h => rw [h]; norm_num
    have h_sum_ge_2 : (List.ofFn fun v : Fin n => x (ls_cellIndex n c v)).sum ≥ 2 := by
      have h_eq_finset : (List.ofFn fun v : Fin n => x (ls_cellIndex n c v)).sum =
                         (Finset.univ : Finset (Fin n)).sum (fun v => x (ls_cellIndex n c v)) := by
        have : (List.ofFn fun v : Fin n => x (ls_cellIndex n c v)) =
               List.map (fun v => x (ls_cellIndex n c v)) (List.finRange n) := by
          rw [List.ofFn_eq_map]
        rw [this]
        rw [← List.sum_toFinset _ (List.nodup_finRange n)]
        congr 1
        exact List.toFinset_finRange n
      rw [h_eq_finset]
      have h_decomp : (Finset.univ : Finset (Fin n)).sum (fun v => x (ls_cellIndex n c v)) =
                      x (ls_cellIndex n c v₁) + x (ls_cellIndex n c v₂) +
                      ((Finset.univ : Finset (Fin n)) \ {v₁, v₂}).sum (fun v => x (ls_cellIndex n c v)) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ {v₁, v₂})]
        have h_pair_sum : ({v₁, v₂} : Finset (Fin n)).sum (fun v => x (ls_cellIndex n c v)) =
                          x (ls_cellIndex n c v₁) + x (ls_cellIndex n c v₂) := by
          rw [Finset.sum_pair h_ne]
        rw [h_pair_sum, add_comm]
      rw [h_decomp]
      have h_rest_nonneg : 0 ≤ ((Finset.univ : Finset (Fin n)) \ {v₁, v₂}).sum
          (fun v => x (ls_cellIndex n c v)) := by
        apply Finset.sum_nonneg
        intros v _
        exact h_nonneg v
      linarith
    linarith
  obtain ⟨v_wit, h_wit⟩ := h_exists
  exact ⟨v_wit, h_wit, fun v' h_v' => (h_unique v_wit v' h_wit h_v').symm⟩

/-- π∘lift round-trip -/
lemma ls_π_lift_inverse (a : IntAssignment (n*n))
    (h_bounds : ∀ c : Fin (n*n), 0 ≤ a c ∧ a c < n) :
    ls_π (ls_lift h_n a) = a := by
  funext c
  unfold ls_π
  have h_c := h_bounds c
  have h_toNat_eq : ((a c).toNat : ℤ) = a c := Int.toNat_of_nonneg h_c.1
  let c_target : Fin n := ⟨(a c).toNat, by
    exact (Int.toNat_lt h_c.1).mpr h_c.2⟩
  have h_find : (List.finRange n).find? (fun v =>
      (ls_lift h_n a) (ls_cellIndex n c v) = 1) = some c_target := by
    have h_eq : List.finRange n = List.ofFn id := rfl
    rw [h_eq]
    have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin n) n id
      (fun v => decide ((ls_lift h_n a) (ls_cellIndex n c v) = 1))
      c_target Function.injective_id
    simp only [id_eq] at h_lem
    rw [h_lem]
    constructor
    · simp only [decide_eq_true_eq]
      unfold ls_lift
      have h_mod := ls_cellIndex_mod c c_target
      have h_div := ls_cellIndex_div c c_target
      simp only [h_mod, ite_eq_left_iff]
      intro h_ne
      exfalso
      apply h_ne
      have : a c = (c_target.val : ℤ) := by simp [c_target, h_toNat_eq]
      have h_c_fin : ⟨(ls_cellIndex n c c_target).val / n, by
        rw [h_div]; exact c.isLt⟩ = c := by simp [h_div]
      rw [h_c_fin]
      exact this
    · intro v' h_v'_lt
      simp only [decide_eq_true_eq]
      unfold ls_lift
      have h_mod := ls_cellIndex_mod c v'
      have h_div := ls_cellIndex_div c v'
      simp only [h_mod]
      intro h_eq'
      have h_target_eq : a c = (c_target.val : ℤ) := by simp [c_target, h_toNat_eq]
      have h_c_fin : ⟨(ls_cellIndex n c v').val / n, by
        rw [h_div]; exact c.isLt⟩ = c := by ext; simp [h_div]
      rw [h_c_fin] at h_eq'
      have h_cond : a c = (v'.val : ℤ) := by
        by_contra h_ne
        simp [h_ne] at h_eq'
      have : (v'.val : ℤ) = (c_target.val : ℤ) := by rw [← h_cond, h_target_eq]
      have : v'.val = c_target.val := by omega
      have : v' = c_target := Fin.ext this
      omega
  rw [h_find]
  simp
  rw [← h_toNat_eq]

/-- Compact solution has valid bounds -/
lemma ls_compact_bounds (a : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_csp n) a)
    (c : Fin (n*n)) :
    0 ≤ a c ∧ a c < n := by
  have h_mem : bound c 0 (n-1) ∈ (latin_square_csp n).constraints := by
    unfold latin_square_csp bound_constraints
    simp only [List.mem_append, List.mem_map, List.mem_finRange, true_and]
    left; left
    exact ⟨c, rfl⟩
  have h_sat := (bound_holds_iff _ _ _ _).mp (h_sol (bound c 0 (n-1)) h_mem)
  constructor
  · exact h_sat.1
  · have h_ub : a c ≤ (n : ℤ) - 1 := h_sat.2
    linarith

/-- find? on finRange produces the correct value for π -/
lemma ls_π_eq_of_unique (x : IntAssignment (n*n*n))
    (_h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (c : Fin (n*n)) (v_wit : Fin n)
    (h_wit : x (ls_cellIndex n c v_wit) = 1)
    (h_uniq : ∀ v', x (ls_cellIndex n c v') = 1 → v' = v_wit) :
    ls_π x c = v_wit.val := by
  unfold ls_π
  have h_find : (List.finRange n).find? (fun v => x (ls_cellIndex n c v) = 1) = some v_wit := by
    rw [show List.finRange n = List.ofFn id from rfl]
    have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin n) n id
      (fun v => decide (x (ls_cellIndex n c v) = 1))
      v_wit Function.injective_id
    simp only [id_eq] at h_lem
    rw [h_lem]
    constructor
    · simp [h_wit]
    · intro v' h_v'_lt
      simp only [decide_eq_true_eq]
      intro h_v'_sat
      have := h_uniq v' h_v'_sat
      rw [this] at h_v'_lt
      exact absurd h_v'_lt (Nat.lt_irrefl _)
  simp [h_find]

end GenericInfrastructure

-- ============================================================================
-- Forward Direction: Expanded → Compact
-- ============================================================================

section Forward

variable {n : ℕ} (h_n : 0 < n)

/-- Row-value sum constraint from solution -/
lemma ls_row_value_sum (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (i v : Fin n) :
    (List.ofFn fun j : Fin n => x (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v)).sum = 1 := by
  have h_mem : sum_eq (ls_row_value_vars n i v) 1 ∈
      (latin_square_matrix n).constraints := by
    unfold latin_square_matrix
    apply List.mem_append_left
    apply List.mem_append_right
    unfold ls_row_value_constraints
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨i, v, rfl⟩
  have h_sat := (sum_eq_holds_iff _ _ _).mp (h_sol (sum_eq (ls_row_value_vars n i v) 1) h_mem)
  simp only [ls_row_value_vars, latin_square_matrix, CSP.L2S.VarType] at h_sat
  rw [_root_.Vector.toList_ofFn] at h_sat
  simpa [Function.comp_def, List.map_ofFn] using h_sat

/-- Column-value sum constraint from solution -/
lemma ls_col_value_sum (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (j v : Fin n) :
    (List.ofFn fun i : Fin n => x (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v)).sum = 1 := by
  have h_mem : sum_eq (ls_col_value_vars n j v) 1 ∈
      (latin_square_matrix n).constraints := by
    unfold latin_square_matrix
    apply List.mem_append_right
    unfold ls_col_value_constraints
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨j, v, rfl⟩
  have h_sat := (sum_eq_holds_iff _ _ _).mp (h_sol (sum_eq (ls_col_value_vars n j v) 1) h_mem)
  simp only [ls_col_value_vars, latin_square_matrix, CSP.L2S.VarType] at h_sat
  rw [_root_.Vector.toList_ofFn] at h_sat
  simpa [Function.comp_def, List.map_ofFn] using h_sat

/-- Forward: row alldifferent -/
lemma ls_forward_row_alldifferent (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (i : Fin n) :
    (List.ofFn fun j : Fin n => ls_π x ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩).Nodup := by
  rw [List.nodup_ofFn]
  intro j₁ j₂ h_eq
  -- Extract the unique values for each cell
  let c₁ : Fin (n*n) := ⟨i.val * n + j₁.val, by
    calc i.val * n + j₁.val
        < i.val * n + n := Nat.add_lt_add_left j₁.isLt _
      _ = (i.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩
  let c₂ : Fin (n*n) := ⟨i.val * n + j₂.val, by
    calc i.val * n + j₂.val
        < i.val * n + n := Nat.add_lt_add_left j₂.isLt _
      _ = (i.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩
  obtain ⟨v₁, hv₁_wit, hv₁_uniq⟩ := ls_one_hot_exactly_one x h_sol c₁
  obtain ⟨v₂, hv₂_wit, hv₂_uniq⟩ := ls_one_hot_exactly_one x h_sol c₂
  -- π gives v₁ and v₂
  have hπ₁ : ls_π x c₁ = v₁.val :=
    ls_π_eq_of_unique x h_sol c₁ v₁ hv₁_wit (fun v' h => hv₁_uniq v' h)
  have hπ₂ : ls_π x c₂ = v₂.val :=
    ls_π_eq_of_unique x h_sol c₂ v₂ hv₂_wit (fun v' h => hv₂_uniq v' h)
  -- From h_eq: π gives same value for both cells
  have h_v_eq : v₁ = v₂ := by
    apply Fin.ext
    have : (v₁.val : ℤ) = (v₂.val : ℤ) := by
      rw [← hπ₁, ← hπ₂]; exact h_eq
    exact Nat.cast_injective this
  -- Both cells have 1 at position v₁
  have h_both_one : x (ls_cellIndex n c₁ v₁) = 1 ∧ x (ls_cellIndex n c₂ v₁) = 1 := by
    exact ⟨hv₁_wit, h_v_eq ▸ hv₂_wit⟩
  -- Use row-value constraint: sum for (row i, value v₁) = 1
  have h_rv_sum := ls_row_value_sum x h_sol i v₁
  -- But sum includes two 1's, contradiction
  have h_binary := fun idx => ls_binary_values x h_sol idx
  have h_nonneg : ∀ j : Fin n, 0 ≤ x (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v₁) := by
    intro j
    cases h_binary (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁) with
    | inl h => rw [h]
    | inr h => rw [h]; norm_num
  by_contra h_ne
  have h_sum_ge_2 : (List.ofFn fun j : Fin n => x (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v₁)).sum ≥ 2 := by
    have h_eq_finset : (List.ofFn fun j : Fin n => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)).sum =
                       (Finset.univ : Finset (Fin n)).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) := by
      rw [List.ofFn_eq_map, ← List.sum_toFinset _ (List.nodup_finRange n)]
      congr 1
      exact List.toFinset_finRange n
    rw [h_eq_finset]
    calc (Finset.univ : Finset (Fin n)).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁))
        ≥ x (ls_cellIndex n ⟨i.val * n + j₁.val, ls_cell_lt i j₁⟩ v₁) + x (ls_cellIndex n ⟨i.val * n + j₂.val, ls_cell_lt i j₂⟩ v₁) := by
          have h_pair : ({j₁, j₂} : Finset (Fin n)).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) =
                        x (ls_cellIndex n ⟨i.val * n + j₁.val, ls_cell_lt i j₁⟩ v₁) + x (ls_cellIndex n ⟨i.val * n + j₂.val, ls_cell_lt i j₂⟩ v₁) := by
            rw [Finset.sum_pair h_ne]
          rw [← h_pair]
          calc (Finset.univ : Finset (Fin n)).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁))
              = ({j₁, j₂} : Finset (Fin n)).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) +
                ((Finset.univ : Finset (Fin n)) \ {j₁, j₂}).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) := by
                  rw [← Finset.sum_sdiff (Finset.subset_univ {j₁, j₂})]
                  ring
            _ ≥ ({j₁, j₂} : Finset (Fin n)).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) + 0 := by
                  apply add_le_add_right
                  exact Finset.sum_nonneg (fun j _ => h_nonneg j)
            _ = ({j₁, j₂} : Finset (Fin n)).sum (fun j => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) := by ring
      _ = 1 + 1 := by rw [h_both_one.1, h_both_one.2]
      _ = 2 := by norm_num
  linarith

/-- Forward: column alldifferent -/
lemma ls_forward_col_alldifferent (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (j : Fin n) :
    (List.ofFn fun i : Fin n => ls_π x ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩).Nodup := by
  rw [List.nodup_ofFn]
  intro i₁ i₂ h_eq
  let c₁ : Fin (n*n) := ⟨i₁.val * n + j.val, by
    calc i₁.val * n + j.val
        < i₁.val * n + n := Nat.add_lt_add_left j.isLt _
      _ = (i₁.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i₁.isLt)⟩
  let c₂ : Fin (n*n) := ⟨i₂.val * n + j.val, by
    calc i₂.val * n + j.val
        < i₂.val * n + n := Nat.add_lt_add_left j.isLt _
      _ = (i₂.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i₂.isLt)⟩
  obtain ⟨v₁, hv₁_wit, hv₁_uniq⟩ := ls_one_hot_exactly_one x h_sol c₁
  obtain ⟨v₂, hv₂_wit, hv₂_uniq⟩ := ls_one_hot_exactly_one x h_sol c₂
  have hπ₁ : ls_π x c₁ = v₁.val :=
    ls_π_eq_of_unique x h_sol c₁ v₁ hv₁_wit (fun v' h => hv₁_uniq v' h)
  have hπ₂ : ls_π x c₂ = v₂.val :=
    ls_π_eq_of_unique x h_sol c₂ v₂ hv₂_wit (fun v' h => hv₂_uniq v' h)
  have h_v_eq : v₁ = v₂ := by
    apply Fin.ext
    have : (v₁.val : ℤ) = (v₂.val : ℤ) := by rw [← hπ₁, ← hπ₂]; exact h_eq
    exact Nat.cast_injective this
  have h_both_one : x (ls_cellIndex n c₁ v₁) = 1 ∧ x (ls_cellIndex n c₂ v₁) = 1 :=
    ⟨hv₁_wit, h_v_eq ▸ hv₂_wit⟩
  have h_cv_sum := ls_col_value_sum x h_sol j v₁
  have h_binary := fun idx => ls_binary_values x h_sol idx
  have h_nonneg : ∀ i : Fin n, 0 ≤ x (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v₁) := by
    intro i
    cases h_binary (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁) with
    | inl h => rw [h]
    | inr h => rw [h]; norm_num
  by_contra h_ne
  have h_sum_ge_2 : (List.ofFn fun i : Fin n => x (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v₁)).sum ≥ 2 := by
    have h_eq_finset : (List.ofFn fun i : Fin n => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)).sum =
                       (Finset.univ : Finset (Fin n)).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) := by
      rw [List.ofFn_eq_map, ← List.sum_toFinset _ (List.nodup_finRange n)]
      congr 1
      exact List.toFinset_finRange n
    rw [h_eq_finset]
    calc (Finset.univ : Finset (Fin n)).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁))
        ≥ x (ls_cellIndex n ⟨i₁.val * n + j.val, ls_cell_lt i₁ j⟩ v₁) + x (ls_cellIndex n ⟨i₂.val * n + j.val, ls_cell_lt i₂ j⟩ v₁) := by
          have h_pair : ({i₁, i₂} : Finset (Fin n)).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) =
                        x (ls_cellIndex n ⟨i₁.val * n + j.val, ls_cell_lt i₁ j⟩ v₁) + x (ls_cellIndex n ⟨i₂.val * n + j.val, ls_cell_lt i₂ j⟩ v₁) := by
            rw [Finset.sum_pair h_ne]
          rw [← h_pair]
          calc (Finset.univ : Finset (Fin n)).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁))
              = ({i₁, i₂} : Finset (Fin n)).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) +
                ((Finset.univ : Finset (Fin n)) \ {i₁, i₂}).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) := by
                  rw [← Finset.sum_sdiff (Finset.subset_univ {i₁, i₂})]
                  ring
            _ ≥ ({i₁, i₂} : Finset (Fin n)).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) + 0 := by
                  apply add_le_add_right
                  exact Finset.sum_nonneg (fun i _ => h_nonneg i)
            _ = ({i₁, i₂} : Finset (Fin n)).sum (fun i => x (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v₁)) := by ring
      _ = 1 + 1 := by rw [h_both_one.1, h_both_one.2]
      _ = 2 := by norm_num
  linarith

/-- Forward: π bounds -/
lemma ls_forward_bounds (x : IntAssignment (n*n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_matrix n) x)
    (c : Fin (n*n)) :
    0 ≤ ls_π x c ∧ ls_π x c ≤ (n : ℤ) - 1 := by
  obtain ⟨v_wit, hv_wit, hv_uniq⟩ := ls_one_hot_exactly_one x h_sol c
  have hπ : ls_π x c = v_wit.val :=
    ls_π_eq_of_unique x h_sol c v_wit hv_wit (fun v' h => hv_uniq v' h)
  rw [hπ]
  constructor
  · exact Int.natCast_nonneg _
  · have : (↑v_wit.val : ℤ) < ↑n := Int.ofNat_lt.mpr v_wit.isLt
    linarith

/-- Forward direction: expanded solution → compact solution -/
theorem ls_forward (sol₂ : IntAssignment (n*n*n))
    (h_sol₂ : IntCSP.isSolutionInt (latin_square_matrix n) sol₂) :
    IntCSP.isSolutionInt (latin_square_csp n) (ls_π sol₂) := by
  unfold IntCSP.isSolutionInt
  intro tc h_tc
  unfold latin_square_csp at h_tc
  simp only [List.mem_append] at h_tc
  rcases h_tc with (h_bound | h_row) | h_col
  · -- Bounds
    obtain ⟨c, ⟨_, h_eq⟩⟩ := (List.mem_map.mp h_bound)
    subst h_eq
    show IntCSP.satisfiesConstraintInt (bound c 0 ((n : ℤ) - 1)) (ls_π sol₂)
    rw [bound_holds_iff]
    exact ls_forward_bounds sol₂ h_sol₂ c
  · -- Row alldifferent
    unfold row_constraints at h_row
    simp only [List.mem_map, List.mem_finRange] at h_row
    obtain ⟨r, _, rfl⟩ := h_row
    show IntCSP.satisfiesConstraintInt (alldifferent (row_variables r)) (ls_π sol₂)
    rw [alldifferent_holds_iff]
    unfold row_variables
    simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
    have := ls_forward_row_alldifferent sol₂ h_sol₂ r
    simpa [Function.comp_def] using this
  · -- Column alldifferent
    unfold col_constraints at h_col
    simp only [List.mem_map, List.mem_finRange] at h_col
    obtain ⟨c, _, rfl⟩ := h_col
    show IntCSP.satisfiesConstraintInt (alldifferent (col_variables c)) (ls_π sol₂)
    rw [alldifferent_holds_iff]
    unfold col_variables
    simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
    have := ls_forward_col_alldifferent sol₂ h_sol₂ c
    simpa [Function.comp_def] using this

end Forward

-- ============================================================================
-- Backward Direction: Compact → Expanded
-- ============================================================================

section Backward

variable {n : ℕ} (h_n : 0 < n)

/-- Backward: row-value sum = 1.
    Key insight: alldifferent + bounds [0,n-1] → injective on Fin n → bijective → each value appears once -/
lemma ls_backward_row_value (a : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_csp n) a)
    (i v : Fin n) :
    (List.ofFn fun j : Fin n => ls_lift h_n a (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v)).sum = 1 := by
  -- Expand lift definitions
  have h_term : ∀ j : Fin n, ls_lift h_n a (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v) =
      if a ⟨i.val * n + j.val, ls_cell_lt i j⟩ = v.val then (1 : ℤ) else 0 := by
    intro j
    unfold ls_lift
    have h_div := ls_cellIndex_div ⟨i.val * n + j.val, ls_cell_lt i j⟩ v
    have h_mod := ls_cellIndex_mod ⟨i.val * n + j.val, ls_cell_lt i j⟩ v
    simp only [h_mod]
    have h_cell_fin : (⟨(ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v).val / n, by
      rw [Nat.div_lt_iff_lt_mul h_n]
      exact (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v).isLt⟩ : Fin (n*n)) =
      ⟨i.val * n + j.val, ls_cell_lt i j⟩ := by ext; exact h_div
    rw [h_cell_fin]
  simp only [h_term]
  -- Row alldifferent gives us injectivity of j ↦ a(i*n+j)
  have h_row_nodup : (List.ofFn fun j : Fin n => a ⟨i.val * n + j.val, ls_cell_lt i j⟩).Nodup := by
    have h_mem : alldifferent (row_variables i) ∈ (latin_square_csp n).constraints := by
      unfold latin_square_csp row_constraints
      simp only [List.mem_append, List.mem_map, List.mem_finRange]
      left; right
      exact ⟨i, trivial, rfl⟩
    have h := (alldifferent_holds_iff _ _).mp (h_sol (alldifferent (row_variables i)) h_mem)
    simp only [row_variables, latin_square_csp, CSP.L2S.VarType] at h
    rw [_root_.Vector.toList_ofFn] at h
    simpa [Function.comp_def, List.map_ofFn] using h
  have h_inj : Function.Injective (fun j : Fin n => a ⟨i.val * n + j.val, ls_cell_lt i j⟩) := by
    exact (List.nodup_ofFn).mp h_row_nodup
  -- Each value is in [0, n-1], so we have Fin n → Fin n (via toNat)
  have h_bounds : ∀ j : Fin n, 0 ≤ a ⟨i.val * n + j.val, ls_cell_lt i j⟩ ∧ a ⟨i.val * n + j.val, ls_cell_lt i j⟩ < n := by
    intro j
    exact ls_compact_bounds a h_sol ⟨i.val * n + j.val, ls_cell_lt i j⟩
  -- Define the function as Fin n → Fin n
  let f : Fin n → Fin n := fun j =>
    ⟨(a ⟨i.val * n + j.val, ls_cell_lt i j⟩).toNat, by
      exact (Int.toNat_lt (h_bounds j).1).mpr (h_bounds j).2⟩
  -- f is injective
  have h_f_inj : Function.Injective f := by
    intro j₁ j₂ h_eq
    have : f j₁ = f j₂ := h_eq
    have h_val_eq : (a ⟨i.val * n + j₁.val, ls_cell_lt i j₁⟩).toNat = (a ⟨i.val * n + j₂.val, ls_cell_lt i j₂⟩).toNat := by
      exact Fin.val_eq_of_eq this
    have h_int_eq : a ⟨i.val * n + j₁.val, ls_cell_lt i j₁⟩ = a ⟨i.val * n + j₂.val, ls_cell_lt i j₂⟩ := by
      have h1 := Int.toNat_of_nonneg (h_bounds j₁).1
      have h2 := Int.toNat_of_nonneg (h_bounds j₂).1
      rw [← h1, ← h2, h_val_eq]
    exact h_inj h_int_eq
  -- Injective on Fin n → surjective
  have h_f_surj : Function.Surjective f := by
    haveI : Finite (Fin n) := Finite.intro (Equiv.refl (Fin n))
    exact Finite.surjective_of_injective h_f_inj
  -- v has exactly one preimage
  obtain ⟨j₀, hj₀⟩ := h_f_surj v
  -- Exactly one j₀ maps to v
  have h_j₀_eq : a ⟨i.val * n + j₀.val, ls_cell_lt i j₀⟩ = v.val := by
    have h_simp := congr_arg Fin.val hj₀
    simp [f] at h_simp
    have h_nonneg := Int.toNat_of_nonneg (h_bounds j₀).1
    rw [← h_nonneg, h_simp]
  have h_others : ∀ j : Fin n, j ≠ j₀ → a ⟨i.val * n + j.val, ls_cell_lt i j⟩ ≠ v.val := by
    intro j h_ne h_eq
    have h_j_eq : f j = v := by
      apply Fin.ext; simp [f]
      have h_nonneg := Int.toNat_of_nonneg (h_bounds j).1
      exact_mod_cast h_nonneg.trans h_eq
    have h_j₀_eq' : f j₀ = v := hj₀
    have := h_f_inj (h_j_eq.trans h_j₀_eq'.symm)
    exact h_ne this
  -- Sum = 1
  trans ((List.ofFn fun j : Fin n => if j = j₀ then (1 : ℤ) else 0).sum)
  · congr 1; congr 1
    funext j
    by_cases h : a ⟨i.val * n + j.val, ls_cell_lt i j⟩ = ↑v.val
    · have : j = j₀ := by
        by_contra h_ne
        exact h_others j h_ne h
      rw [if_pos h, if_pos this]
    · have : j ≠ j₀ := by
        intro h_eq; rw [h_eq] at h; exact h h_j₀_eq
      rw [if_neg h, if_neg this]
  · rw [List.ofFn_eq_map, ← List.sum_toFinset _ (List.nodup_finRange n),
          List.toFinset_finRange, Finset.sum_eq_single j₀]
    · simp
    · intro b _ h_ne; simp [h_ne]
    · intro h_mem; exfalso; exact h_mem (Finset.mem_univ j₀)

/-- Backward: col-value sum = 1 -/
lemma ls_backward_col_value (a : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (latin_square_csp n) a)
    (j v : Fin n) :
    (List.ofFn fun i : Fin n => ls_lift h_n a (ls_cellIndex n ⟨i.val * n + j.val, by
      calc i.val * n + j.val
          < i.val * n + n := Nat.add_lt_add_left j.isLt _
        _ = (i.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩ v)).sum = 1 := by
  have h_term : ∀ i : Fin n, ls_lift h_n a (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v) =
      if a ⟨i.val * n + j.val, ls_cell_lt i j⟩ = v.val then (1 : ℤ) else 0 := by
    intro i
    unfold ls_lift
    have h_div := ls_cellIndex_div ⟨i.val * n + j.val, ls_cell_lt i j⟩ v
    have h_mod := ls_cellIndex_mod ⟨i.val * n + j.val, ls_cell_lt i j⟩ v
    simp only [h_mod]
    have h_cell_fin : (⟨(ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v).val / n, by
      rw [Nat.div_lt_iff_lt_mul h_n]
      exact (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v).isLt⟩ : Fin (n*n)) =
      ⟨i.val * n + j.val, ls_cell_lt i j⟩ := by ext; exact h_div
    rw [h_cell_fin]
  simp only [h_term]
  -- Column alldifferent gives injectivity of i ↦ a(i*n+j)
  have h_col_nodup : (List.ofFn fun i : Fin n => a ⟨i.val * n + j.val, ls_cell_lt i j⟩).Nodup := by
    have h_mem : alldifferent (col_variables j) ∈ (latin_square_csp n).constraints := by
      unfold latin_square_csp col_constraints
      simp only [List.mem_append, List.mem_map, List.mem_finRange]
      right
      exact ⟨j, trivial, rfl⟩
    have h := (alldifferent_holds_iff _ _).mp (h_sol (alldifferent (col_variables j)) h_mem)
    simp only [col_variables, latin_square_csp, CSP.L2S.VarType] at h
    rw [_root_.Vector.toList_ofFn] at h
    simpa [Function.comp_def, List.map_ofFn] using h
  have h_inj : Function.Injective (fun i : Fin n => a ⟨i.val * n + j.val, ls_cell_lt i j⟩) :=
    (List.nodup_ofFn).mp h_col_nodup
  have h_bounds : ∀ i : Fin n, 0 ≤ a ⟨i.val * n + j.val, ls_cell_lt i j⟩ ∧ a ⟨i.val * n + j.val, ls_cell_lt i j⟩ < n := by
    intro i
    exact ls_compact_bounds a h_sol ⟨i.val * n + j.val, ls_cell_lt i j⟩
  let f : Fin n → Fin n := fun i =>
    ⟨(a ⟨i.val * n + j.val, ls_cell_lt i j⟩).toNat, by
      exact (Int.toNat_lt (h_bounds i).1).mpr (h_bounds i).2⟩
  have h_f_inj : Function.Injective f := by
    intro i₁ i₂ h_eq
    have h_val_eq : (a ⟨i₁.val * n + j.val, ls_cell_lt i₁ j⟩).toNat = (a ⟨i₂.val * n + j.val, ls_cell_lt i₂ j⟩).toNat :=
      Fin.val_eq_of_eq h_eq
    have h_int_eq : a ⟨i₁.val * n + j.val, ls_cell_lt i₁ j⟩ = a ⟨i₂.val * n + j.val, ls_cell_lt i₂ j⟩ := by
      have h1 := Int.toNat_of_nonneg (h_bounds i₁).1
      have h2 := Int.toNat_of_nonneg (h_bounds i₂).1
      rw [← h1, ← h2, h_val_eq]
    exact h_inj h_int_eq
  have h_f_surj : Function.Surjective f := by
    haveI : Finite (Fin n) := Finite.intro (Equiv.refl (Fin n))
    exact Finite.surjective_of_injective h_f_inj
  obtain ⟨i₀, hi₀⟩ := h_f_surj v
  have h_i₀_eq : a ⟨i₀.val * n + j.val, ls_cell_lt i₀ j⟩ = v.val := by
    have h_simp := congr_arg Fin.val hi₀
    simp [f] at h_simp
    have h_nonneg := Int.toNat_of_nonneg (h_bounds i₀).1
    rw [← h_nonneg, h_simp]
  have h_others : ∀ i : Fin n, i ≠ i₀ → a ⟨i.val * n + j.val, ls_cell_lt i j⟩ ≠ v.val := by
    intro i h_ne h_eq
    have h_i_eq : f i = v := by
      apply Fin.ext; simp [f]
      have h_nonneg := Int.toNat_of_nonneg (h_bounds i).1
      exact_mod_cast h_nonneg.trans h_eq
    have h_i₀_eq' : f i₀ = v := hi₀
    exact h_ne (h_f_inj (h_i_eq.trans h_i₀_eq'.symm))
  trans ((List.ofFn fun i : Fin n => if i = i₀ then (1 : ℤ) else 0).sum)
  · congr 1; congr 1
    funext i
    by_cases h : a ⟨i.val * n + j.val, ls_cell_lt i j⟩ = ↑v.val
    · have : i = i₀ := by by_contra h_ne; exact h_others i h_ne h
      rw [if_pos h, if_pos this]
    · have : i ≠ i₀ := by intro h_eq; rw [h_eq] at h; exact h h_i₀_eq
      rw [if_neg h, if_neg this]
  · rw [List.ofFn_eq_map, ← List.sum_toFinset _ (List.nodup_finRange n),
          List.toFinset_finRange, Finset.sum_eq_single i₀]
    · simp
    · intro b _ h_ne; simp [h_ne]
    · intro h_mem; exfalso; exact h_mem (Finset.mem_univ i₀)

/-- The lift satisfies the LS matrix constraints (extracted for reuse by Sudoku) -/
lemma ls_lift_satisfies_matrix (sol₁ : IntAssignment (n*n)) (h_n : 0 < n)
    (h_sol₁ : IntCSP.isSolutionInt (latin_square_csp n) sol₁) :
    (latin_square_matrix n).isSolutionInt (ls_lift h_n sol₁) := by
  unfold IntCSP.isSolutionInt
  intro tc h_tc
  unfold latin_square_matrix at h_tc
  unfold ls_binary_bounds ls_cell_one_hot ls_row_value_constraints ls_col_value_constraints at h_tc
  simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_flatMap, true_and] at h_tc
  rcases h_tc with ((⟨idx, h_eq⟩ | ⟨c, h_eq⟩) | ⟨i, v, h_eq⟩) | ⟨j, v, h_eq⟩
  · -- Binary bounds
    subst h_eq
    show IntCSP.satisfiesConstraintInt (bound idx 0 1) (ls_lift h_n sol₁)
    rw [bound_holds_iff]
    show 0 ≤ ls_lift h_n sol₁ idx ∧ ls_lift h_n sol₁ idx ≤ 1
    unfold ls_lift
    simp only
    split_ifs <;> constructor <;> norm_num
  · -- Cell one-hot
    subst h_eq
    show IntCSP.satisfiesConstraintInt (sum_eq (ls_cell_vars n c) 1) (ls_lift h_n sol₁)
    rw [sum_eq_holds_iff]
    unfold ls_cell_vars
    simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
    show (List.ofFn fun v : Fin n => ls_lift h_n sol₁ (ls_cellIndex n c v)).sum = 1
    have h_bounds := ls_compact_bounds sol₁ h_sol₁ c
    have h_toNat_eq : ((sol₁ c).toNat : ℤ) = sol₁ c := Int.toNat_of_nonneg h_bounds.1
    let v_target : Fin n := ⟨(sol₁ c).toNat, by
      exact (Int.toNat_lt h_bounds.1).mpr h_bounds.2⟩
    have h_term : ∀ v : Fin n, ls_lift h_n sol₁ (ls_cellIndex n c v) =
        if v = v_target then (1 : ℤ) else 0 := by
      intro v
      unfold ls_lift
      have h_div := ls_cellIndex_div c v
      have h_mod := ls_cellIndex_mod c v
      simp only [h_mod]
      have h_cell_fin : (⟨(ls_cellIndex n c v).val / n, by
        rw [Nat.div_lt_iff_lt_mul h_n]
        exact (ls_cellIndex n c v).isLt⟩ : Fin (n*n)) = c := by ext; exact h_div
      rw [h_cell_fin]
      have h_cast_eq : sol₁ c = ↑v.val ↔ v = v_target := by
        constructor
        · intro h
          apply Fin.ext; simp [v_target]
          have : Int.toNat (sol₁ c) = Int.toNat (↑v.val : ℤ) := by rw [h]
          rw [this, Int.toNat_natCast]
        · intro h
          rw [h]; simp [v_target, h_toNat_eq]
      by_cases h : sol₁ c = ↑v.val
      · rw [if_pos h, if_pos (h_cast_eq.mp h)]
      · rw [if_neg h, if_neg (mt h_cast_eq.mpr h)]
    simp only [h_term]
    rw [List.ofFn_eq_map, ← List.sum_toFinset _ (List.nodup_finRange n),
        List.toFinset_finRange, Finset.sum_eq_single v_target]
    · simp
    · intro b _ h_ne; simp [h_ne]
    · intro h_mem; exfalso; exact h_mem (Finset.mem_univ v_target)
  · -- Row-value constraint
    subst h_eq
    show IntCSP.satisfiesConstraintInt (sum_eq (ls_row_value_vars n i v) 1) (ls_lift h_n sol₁)
    rw [sum_eq_holds_iff]
    unfold ls_row_value_vars
    simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
    show (List.ofFn fun j : Fin n => ls_lift h_n sol₁ (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v)).sum = 1
    exact ls_backward_row_value h_n sol₁ h_sol₁ i v
  · -- Col-value constraint
    subst h_eq
    show IntCSP.satisfiesConstraintInt (sum_eq (ls_col_value_vars n j v) 1) (ls_lift h_n sol₁)
    rw [sum_eq_holds_iff]
    unfold ls_col_value_vars
    simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
    show (List.ofFn fun i : Fin n => ls_lift h_n sol₁ (ls_cellIndex n ⟨i.val * n + j.val, ls_cell_lt i j⟩ v)).sum = 1
    exact ls_backward_col_value h_n sol₁ h_sol₁ j v

theorem ls_backward (sol₁ : IntAssignment (n*n)) (h_n : 0 < n)
    (h_sol₁ : IntCSP.isSolutionInt (latin_square_csp n) sol₁) :
    ∃ sol₂ : IntAssignment (n*n*n),
      IntCSP.isSolutionInt (latin_square_matrix n) sol₂ ∧
      ls_π sol₂ = sol₁ := by
  exact ⟨ls_lift h_n sol₁, ls_lift_satisfies_matrix sol₁ h_n h_sol₁,
    ls_π_lift_inverse h_n sol₁ (fun c => ls_compact_bounds sol₁ h_sol₁ c)⟩

end Backward

-- ============================================================================
-- Injectivity
-- ============================================================================

section Injectivity

variable {n : ℕ} (h_n : 0 < n)

/-- Injectivity: different expanded solutions with same projection are equal -/
theorem ls_injective (sol₂ sol₂' : IntAssignment (n*n*n)) (h_n : 0 < n)
    (h_sol₂ : IntCSP.isSolutionInt (latin_square_matrix n) sol₂)
    (h_sol₂' : IntCSP.isSolutionInt (latin_square_matrix n) sol₂')
    (h_proj_eq : ls_π sol₂ = ls_π sol₂') :
    sol₂ = sol₂' := by
  funext idx
  let c : Fin (n*n) := ⟨idx.val / n, by
    rw [Nat.div_lt_iff_lt_mul h_n]; exact idx.isLt⟩
  let d : Fin n := ⟨idx.val % n, Nat.mod_lt idx.val h_n⟩
  have h_idx_eq : idx = ls_cellIndex n c d := by
    apply Fin.ext
    unfold ls_cellIndex
    simp only
    show idx.val = c.val * n + d.val
    have h_div_mod : idx.val = n * (idx.val / n) + idx.val % n :=
      (Nat.div_add_mod idx.val n).symm
    calc idx.val = n * (idx.val / n) + idx.val % n := h_div_mod
         _ = (idx.val / n) * n + idx.val % n := by rw [Nat.mul_comm]
         _ = c.val * n + d.val := rfl
  obtain ⟨v₂, hv₂_wit, hv₂_uniq⟩ := ls_one_hot_exactly_one sol₂ h_sol₂ c
  obtain ⟨v₂', hv₂'_wit, hv₂'_uniq⟩ := ls_one_hot_exactly_one sol₂' h_sol₂' c
  have h_proj_c : ls_π sol₂ c = ls_π sol₂' c := congrFun h_proj_eq c
  have hπ₂ : ls_π sol₂ c = v₂.val :=
    ls_π_eq_of_unique sol₂ h_sol₂ c v₂ hv₂_wit (fun v' h => hv₂_uniq v' h)
  have hπ₂' : ls_π sol₂' c = v₂'.val :=
    ls_π_eq_of_unique sol₂' h_sol₂' c v₂' hv₂'_wit (fun v' h => hv₂'_uniq v' h)
  have h_v_eq : v₂ = v₂' := by
    apply Fin.ext
    have : (v₂.val : ℤ) = (v₂'.val : ℤ) := by rw [← hπ₂, ← hπ₂', h_proj_c]
    exact Nat.cast_injective this
  rw [h_idx_eq]
  by_cases h_case : d = v₂
  · calc sol₂ (ls_cellIndex n c d)
        = sol₂ (ls_cellIndex n c v₂) := by rw [h_case]
      _ = 1 := hv₂_wit
      _ = sol₂' (ls_cellIndex n c v₂') := hv₂'_wit.symm
      _ = sol₂' (ls_cellIndex n c d) := by rw [← h_v_eq, ← h_case]
  · have h₂_zero : sol₂ (ls_cellIndex n c d) = 0 := by
      cases ls_binary_values sol₂ h_sol₂ (ls_cellIndex n c d) with
      | inl h => exact h
      | inr h =>
        have : d = v₂ := hv₂_uniq d h
        exact absurd this h_case
    have h₂'_zero : sol₂' (ls_cellIndex n c d) = 0 := by
      have h_case' : d ≠ v₂' := by rwa [h_v_eq] at h_case
      cases ls_binary_values sol₂' h_sol₂' (ls_cellIndex n c d) with
      | inl h => exact h
      | inr h =>
        have : d = v₂' := hv₂'_uniq d h
        exact absurd this h_case'
    rw [h₂_zero, h₂'_zero]

end Injectivity

-- ============================================================================
-- Main Theorems
-- ============================================================================

/-- Latin Square formulations are π-equivalent -/
theorem latin_square_pi_equivalent (n : ℕ) (h_n : 0 < n) :
    piEquivalent
      (latin_square_csp n)
      (latin_square_matrix n)
      (@ls_π n) := by
  constructor
  · exact ls_forward
  constructor
  · exact fun sol₁ h_sol₁ => ls_backward sol₁ h_n h_sol₁
  · exact fun sol₂ sol₂' h₁ h₂ h₃ => ls_injective sol₂ sol₂' h_n h₁ h₂ h₃

/-- Derived: Full equivalence -/
theorem latin_square_formulations_equivalent (n : ℕ) (h_n : 0 < n) :
    equivalent
      (latin_square_matrix n)
      (latin_square_csp n) := by
  apply piEquivalent_implies_equivalent
  exact latin_square_pi_equivalent n h_n

/-- Derived: Equisatisfiability -/
theorem latin_square_equisatisfiable_formulations (n : ℕ) (h_n : 0 < n) :
    equisatisfiable
      (latin_square_csp n)
      (latin_square_matrix n) := by
  apply piEquivalent_implies_equisatisfiable
  exact latin_square_pi_equivalent n h_n

end LatinSquare
