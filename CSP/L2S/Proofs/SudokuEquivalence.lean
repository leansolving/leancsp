import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Proofs.LatinSquareSB
import CSP.L2S.Proofs.LatinSquareEquivalence
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
open LatinSquare

namespace Sudoku

/-!
## Sudoku π-Equivalence: Value-Based ↔ One-Hot Binary

Extends Latin Square with box (sub-grid) constraints.

### Parameters
- `b : ℕ` (block size), `n := b * b` (grid size). Standard Sudoku: b=3, n=9.

### Formulation 1 (Compact)
Variables: n² (one per cell), Domain: {0,...,n-1}
Constraints: bounds, row alldiff, col alldiff, box alldiff

### Formulation 2 (Expanded)
Variables: n³ (one per (cell,value) triple), Domain: {0,1}
Constraints: binary bounds, cell one-hot, row-value sum=1, col-value sum=1, box-value sum=1

### π-Equivalence
Same projection/lifting as Latin Square. Box constraints add new proof obligations.
-/

/-! ### Sudoku CSP Definitions -/

section SudokuDefinitions

variable (b : ℕ)

/-- Grid size from block size -/
abbrev gridSize (b : ℕ) : ℕ := b * b

/-- Helper: cell index for box cell (bi, bj, di, dj) in the n×n grid.
    Row = bi*b + di, Col = bj*b + dj, Cell = row*n + col -/
def boxCellIndex (bi bj di dj : Fin b) : Fin (gridSize b * gridSize b) :=
  ⟨(bi.val * b + di.val) * (b * b) + (bj.val * b + dj.val), by
    have hbi := bi.isLt; have hbj := bj.isLt
    have hdi := di.isLt; have hdj := dj.isLt
    have h_row : bi.val * b + di.val < b * b := by nlinarith
    have h_col : bj.val * b + dj.val < b * b := by nlinarith
    nlinarith⟩

/-- Helper: get all b² variables in a box -/
def box_variables (bi bj : Fin b) :
    _root_.Vector (VarType (gridSize b * gridSize b)) (gridSize b) :=
  _root_.Vector.ofFn (fun k : Fin (b * b) =>
    let di : Fin b := ⟨k.val / b, by
      have := k.isLt; exact Nat.div_lt_of_lt_mul this⟩
    let dj : Fin b := ⟨k.val % b, Nat.mod_lt k.val (by have := bi.isLt; omega)⟩
    boxCellIndex b bi bj di dj)

/-- Box constraints: alldifferent within each box -/
def box_constraints : List (IntConstraint (gridSize b * gridSize b)) :=
  (List.finRange b).flatMap fun bi =>
    (List.finRange b).map fun bj =>
      alldifferent (box_variables b bi bj)

/-- Sudoku compact CSP = Latin Square + box constraints -/
def sudoku_csp : IntCSP :=
  ⟨gridSize b * gridSize b,
    bound_constraints (gridSize b) ++
    row_constraints (gridSize b) ++
    col_constraints (gridSize b) ++
    box_constraints b⟩

-- Expanded formulation: add box-value constraints to Latin Square matrix

/-- Box-value variables: for box (bi,bj) and value v, the b² cells with that value.
    Maps k ∈ Fin(b²) to ls_cellIndex of boxCell(bi,bj,k/b,k%b) at value v -/
def sudoku_box_value_vars (bi bj : Fin b) (v : Fin (gridSize b)) :
    _root_.Vector (Fin (gridSize b * gridSize b * gridSize b)) (gridSize b) :=
  _root_.Vector.ofFn (fun k : Fin (b * b) =>
    let di : Fin b := ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
    let dj : Fin b := ⟨k.val % b, Nat.mod_lt k.val (by have := bi.isLt; omega)⟩
    ls_cellIndex (gridSize b) (boxCellIndex b bi bj di dj) v)

/-- Box-value constraints: for each box (bi,bj) and value v, exactly one cell has that value -/
def sudoku_box_value_constraints : List (IntConstraint (gridSize b * gridSize b * gridSize b)) :=
  (List.finRange b).flatMap fun bi =>
    (List.finRange b).flatMap fun bj =>
      (List.finRange (gridSize b)).map fun v =>
        sum_eq (sudoku_box_value_vars b bi bj v) 1

/-- Sudoku expanded CSP = Latin Square matrix + box-value constraints -/
def sudoku_matrix : IntCSP :=
  ⟨gridSize b * gridSize b * gridSize b,
    ls_binary_bounds (gridSize b) ++
    ls_cell_one_hot (gridSize b) ++
    ls_row_value_constraints (gridSize b) ++
    ls_col_value_constraints (gridSize b) ++
    sudoku_box_value_constraints b⟩

end SudokuDefinitions

/-! ### Projection and Lifting (reuse Latin Square) -/

/-- Sudoku projection = Latin Square projection -/
def sudoku_π {b : ℕ} (x : IntAssignment (gridSize b * gridSize b * gridSize b)) :
    IntAssignment (gridSize b * gridSize b) :=
  ls_π x

/-- Sudoku lifting = Latin Square lifting -/
def sudoku_lift {b : ℕ} (h_n : 0 < gridSize b) (a : IntAssignment (gridSize b * gridSize b)) :
    IntAssignment (gridSize b * gridSize b * gridSize b) :=
  ls_lift h_n a

/-! ### Box Indexing Arithmetic -/

section BoxArithmetic

variable {b : ℕ} (h_b : 0 < b)
include h_b

private lemma gridSize_pos : 0 < gridSize b := Nat.mul_pos h_b h_b

/-- The row of boxCellIndex is bi*b + di -/
lemma boxCellIndex_row (bi bj di dj : Fin b) :
    (boxCellIndex b bi bj di dj).val / (b * b) = bi.val * b + di.val := by
  unfold boxCellIndex
  simp only
  have h_col : bj.val * b + dj.val < b * b := by nlinarith [bj.isLt, dj.isLt]
  have h_col_div : (bj.val * b + dj.val) / (b * b) = 0 := Nat.div_eq_of_lt h_col
  rw [show (bi.val * b + di.val) * (b * b) + (bj.val * b + dj.val) =
      (bj.val * b + dj.val) + (bi.val * b + di.val) * (b * b) from by ring]
  rw [Nat.add_mul_div_right _ _ (Nat.mul_pos h_b h_b)]
  omega

omit h_b in
/-- The column of boxCellIndex is bj*b + dj -/
lemma boxCellIndex_col (bi bj di dj : Fin b) :
    (boxCellIndex b bi bj di dj).val % (b * b) = bj.val * b + dj.val := by
  unfold boxCellIndex
  simp only
  have h_col : bj.val * b + dj.val < b * b := by nlinarith [bj.isLt, dj.isLt]
  exact Nat.mul_add_mod_of_lt h_col

/-- boxCellIndex is injective (different (di,dj) → different cells) -/
lemma boxCellIndex_injective (bi bj : Fin b) :
    Function.Injective (fun k : Fin (b * b) =>
      boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                             ⟨k.val % b, Nat.mod_lt k.val h_b⟩) := by
  intro k₁ k₂ h_eq
  have h_val := congrArg Fin.val h_eq
  unfold boxCellIndex at h_val
  simp only at h_val
  -- h_val : (bi*b + k₁/b) * (b*b) + (bj*b + k₁%b) = (bi*b + k₂/b) * (b*b) + (bj*b + k₂%b)
  have h1 : bj.val * b + k₁.val % b < b * b := by
    have := Nat.mod_lt k₁.val h_b; nlinarith [bj.isLt]
  have h2 : bj.val * b + k₂.val % b < b * b := by
    have := Nat.mod_lt k₂.val h_b; nlinarith [bj.isLt]
  -- Column equality: take mod (b*b) of both sides
  have h_col : bj.val * b + k₁.val % b = bj.val * b + k₂.val % b := by
    have lhs := @Nat.mul_add_mod_of_lt (bi.val * b + k₁.val / b) (b * b) _ h1
    have rhs := @Nat.mul_add_mod_of_lt (bi.val * b + k₂.val / b) (b * b) _ h2
    rw [← lhs, ← rhs, h_val]
  -- Row equality via cancellation
  have h_mul_eq : (bi.val * b + k₁.val / b) * (b * b) =
                  (bi.val * b + k₂.val / b) * (b * b) := by linarith
  have h_row : bi.val * b + k₁.val / b = bi.val * b + k₂.val / b :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos h_b h_b) h_mul_eq
  have h_div : k₁.val / b = k₂.val / b := by omega
  have h_mod : k₁.val % b = k₂.val % b := by omega
  exact Fin.ext (calc k₁.val
      _ = b * (k₁.val / b) + k₁.val % b := (Nat.div_add_mod k₁.val b).symm
      _ = b * (k₂.val / b) + k₂.val % b := by rw [h_div, h_mod]
      _ = k₂.val := Nat.div_add_mod k₂.val b)

end BoxArithmetic

/-! ### Infrastructure: Sudoku extends Latin Square -/

section SudokuInfrastructure

variable {b : ℕ} (h_b : 0 < b)
include h_b

private lemma h_gs_pos : 0 < gridSize b := gridSize_pos h_b

omit h_b in
/-- Sudoku compact CSP contains all Latin Square constraints -/
lemma sudoku_csp_contains_ls (tc : IntConstraint (gridSize b * gridSize b))
    (h_tc : tc ∈ (latin_square_csp (gridSize b)).constraints) :
    tc ∈ (sudoku_csp b).constraints := by
  unfold sudoku_csp latin_square_csp at *
  simp only [List.mem_append] at *
  rcases h_tc with (h_b' | h_r) | h_c
  · left; left; left; exact h_b'
  · left; left; right; exact h_r
  · left; right; exact h_c

omit h_b in
/-- Sudoku compact solution is also a Latin Square solution -/
lemma sudoku_sol_is_ls_sol (a : IntAssignment (gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_csp b) a) :
    IntCSP.isSolutionInt (latin_square_csp (gridSize b)) a := by
  intro tc h_tc
  exact h_sol tc (sudoku_csp_contains_ls tc h_tc)

omit h_b in
/-- Sudoku matrix contains all Latin Square matrix constraints -/
lemma sudoku_matrix_contains_ls_matrix (tc : IntConstraint (gridSize b * gridSize b * gridSize b))
    (h_tc : tc ∈ (latin_square_matrix (gridSize b)).constraints) :
    tc ∈ (sudoku_matrix b).constraints := by
  unfold sudoku_matrix latin_square_matrix at *
  simp only [List.mem_append] at *
  rcases h_tc with ((h1 | h2) | h3) | h4
  · left; left; left; left; exact h1
  · left; left; left; right; exact h2
  · left; left; right; exact h3
  · left; right; exact h4

omit h_b in
/-- Sudoku matrix solution is also a Latin Square matrix solution -/
lemma sudoku_matrix_sol_is_ls_sol (x : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_matrix b) x) :
    IntCSP.isSolutionInt (latin_square_matrix (gridSize b)) x := by
  intro tc h_tc
  exact h_sol tc (sudoku_matrix_contains_ls_matrix tc h_tc)

omit h_b in
/-- Binary values from sudoku matrix solution -/
lemma sudoku_binary_values (x : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_matrix b) x)
    (idx : Fin (gridSize b * gridSize b * gridSize b)) :
    x idx = 0 ∨ x idx = 1 :=
  ls_binary_values x (sudoku_matrix_sol_is_ls_sol x h_sol) idx

omit h_b in
/-- One-hot from sudoku matrix solution -/
lemma sudoku_one_hot (x : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_matrix b) x)
    (c : Fin (gridSize b * gridSize b)) :
    ∃! v : Fin (gridSize b), x (ls_cellIndex (gridSize b) c v) = 1 :=
  ls_one_hot_exactly_one x (sudoku_matrix_sol_is_ls_sol x h_sol) c

end SudokuInfrastructure

/-! ### Forward Direction: Expanded → Compact -/

section Forward

variable {b : ℕ} (h_b : 0 < b)
include h_b

/-- Box-value sum constraint from sudoku matrix solution -/
lemma sudoku_box_value_sum (x : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_matrix b) x)
    (bi bj : Fin b) (v : Fin (gridSize b)) :
    (List.ofFn fun k : Fin (b * b) =>
      x (ls_cellIndex (gridSize b)
        (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                               ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v)).sum = 1 := by
  have h_mem : sum_eq (sudoku_box_value_vars b bi bj v) 1 ∈
      (sudoku_matrix b).constraints := by
    unfold sudoku_matrix
    apply List.mem_append_right
    unfold sudoku_box_value_constraints
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨bi, bj, v, rfl⟩
  have h_sat := (sum_eq_holds_iff _ _ _).mp (h_sol (sum_eq (sudoku_box_value_vars b bi bj v) 1) h_mem)
  simp only [sudoku_box_value_vars, sudoku_matrix, CSP.L2S.VarType] at h_sat
  rw [_root_.Vector.toList_ofFn] at h_sat
  simpa [Function.comp_def, List.map_ofFn] using h_sat

/-- Forward: box alldifferent.
    If two cells in the same box have the same π value v, then the box-value sum ≥ 2,
    contradicting sum = 1. -/
lemma sudoku_forward_box_alldifferent (x : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_matrix b) x)
    (bi bj : Fin b) :
    (List.ofFn fun k : Fin (b * b) =>
      sudoku_π x (boxCellIndex b bi bj
        ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
        ⟨k.val % b, Nat.mod_lt k.val h_b⟩)).Nodup := by
  rw [List.nodup_ofFn]
  intro k₁ k₂ h_eq
  let c₁ := boxCellIndex b bi bj ⟨k₁.val / b, Nat.div_lt_of_lt_mul k₁.isLt⟩
                                   ⟨k₁.val % b, Nat.mod_lt k₁.val h_b⟩
  let c₂ := boxCellIndex b bi bj ⟨k₂.val / b, Nat.div_lt_of_lt_mul k₂.isLt⟩
                                   ⟨k₂.val % b, Nat.mod_lt k₂.val h_b⟩
  have h_ls_sol := sudoku_matrix_sol_is_ls_sol x h_sol
  obtain ⟨v₁, hv₁_wit, hv₁_uniq⟩ := ls_one_hot_exactly_one x h_ls_sol c₁
  obtain ⟨v₂, hv₂_wit, hv₂_uniq⟩ := ls_one_hot_exactly_one x h_ls_sol c₂
  have hπ₁ : sudoku_π x c₁ = v₁.val := by
    unfold sudoku_π
    exact ls_π_eq_of_unique x h_ls_sol c₁ v₁ hv₁_wit (fun v' h => hv₁_uniq v' h)
  have hπ₂ : sudoku_π x c₂ = v₂.val := by
    unfold sudoku_π
    exact ls_π_eq_of_unique x h_ls_sol c₂ v₂ hv₂_wit (fun v' h => hv₂_uniq v' h)
  have h_v_eq : v₁ = v₂ := by
    apply Fin.ext
    have : (v₁.val : ℤ) = (v₂.val : ℤ) := by rw [← hπ₁, ← hπ₂]; exact h_eq
    exact Nat.cast_injective this
  -- Both cells have 1 at position v₁
  have h_both_one : x (ls_cellIndex (gridSize b) c₁ v₁) = 1 ∧
                    x (ls_cellIndex (gridSize b) c₂ v₁) = 1 :=
    ⟨hv₁_wit, h_v_eq ▸ hv₂_wit⟩
  -- Use box-value constraint: sum for (box, v₁) = 1
  have h_bv_sum := sudoku_box_value_sum h_b x h_sol bi bj v₁
  have h_nonneg : ∀ k : Fin (b * b), 0 ≤ x (ls_cellIndex (gridSize b)
      (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                             ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v₁) := by
    intro k
    cases sudoku_binary_values x h_sol _ with
    | inl h => rw [h]
    | inr h => rw [h]; norm_num
  by_contra h_ne
  have h_sum_ge_2 : (List.ofFn fun k : Fin (b * b) =>
      x (ls_cellIndex (gridSize b)
        (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                               ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v₁)).sum ≥ 2 := by
    have h_eq_finset : (List.ofFn fun k : Fin (b * b) =>
        x (ls_cellIndex (gridSize b)
          (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                                 ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v₁)).sum =
        (Finset.univ : Finset (Fin (b * b))).sum (fun k =>
          x (ls_cellIndex (gridSize b)
            (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                                   ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v₁)) := by
      rw [List.ofFn_eq_map, ← List.sum_toFinset _ (List.nodup_finRange (b * b))]
      congr 1
      exact List.toFinset_finRange (b * b)
    rw [h_eq_finset]
    have h_pair : ({k₁, k₂} : Finset (Fin (b * b))).sum (fun k =>
        x (ls_cellIndex (gridSize b)
          (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                                 ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v₁)) =
        x (ls_cellIndex (gridSize b) c₁ v₁) + x (ls_cellIndex (gridSize b) c₂ v₁) := by
      rw [Finset.sum_pair h_ne]
    have h_le := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({k₁, k₂} : Finset (Fin (b * b))))
      (fun k _ _ => h_nonneg k)
    linarith [h_pair, h_both_one.1, h_both_one.2]
  linarith

omit h_b in
/-- Forward: π bounds (from Latin Square) -/
lemma sudoku_forward_bounds (x : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_matrix b) x)
    (c : Fin (gridSize b * gridSize b)) :
    0 ≤ sudoku_π x c ∧ sudoku_π x c ≤ (gridSize b : ℤ) - 1 := by
  unfold sudoku_π
  exact ls_forward_bounds x (sudoku_matrix_sol_is_ls_sol x h_sol) c

/-- Forward direction: sudoku matrix solution → sudoku compact solution -/
theorem sudoku_forward (sol₂ : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol₂ : IntCSP.isSolutionInt (sudoku_matrix b) sol₂) :
    IntCSP.isSolutionInt (sudoku_csp b) (sudoku_π sol₂) := by
  unfold IntCSP.isSolutionInt
  intro tc h_tc
  unfold sudoku_csp at h_tc
  simp only [List.mem_append] at h_tc
  rcases h_tc with ((h_bound | h_row) | h_col) | h_box
  · -- Bounds: delegate to Latin Square forward
    have h_ls_sol := sudoku_matrix_sol_is_ls_sol sol₂ h_sol₂
    have h_ls_forward := ls_forward sol₂ h_ls_sol
    unfold latin_square_csp at h_ls_forward
    have : tc ∈ (latin_square_csp (gridSize b)).constraints := by
      unfold latin_square_csp
      exact List.mem_append_left _ (List.mem_append_left _ h_bound)
    exact h_ls_forward tc this
  · -- Row alldiff: delegate to Latin Square forward
    have h_ls_sol := sudoku_matrix_sol_is_ls_sol sol₂ h_sol₂
    have h_ls_forward := ls_forward sol₂ h_ls_sol
    have : tc ∈ (latin_square_csp (gridSize b)).constraints := by
      unfold latin_square_csp
      exact List.mem_append_left _ (List.mem_append_right _ h_row)
    exact h_ls_forward tc this
  · -- Col alldiff: delegate to Latin Square forward
    have h_ls_sol := sudoku_matrix_sol_is_ls_sol sol₂ h_sol₂
    have h_ls_forward := ls_forward sol₂ h_ls_sol
    have : tc ∈ (latin_square_csp (gridSize b)).constraints := by
      unfold latin_square_csp
      exact List.mem_append_right _ h_col
    exact h_ls_forward tc this
  · -- Box alldiff: NEW
    unfold box_constraints at h_box
    simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at h_box
    obtain ⟨bi, bj, rfl⟩ := h_box
    show IntCSP.satisfiesConstraintInt (alldifferent (box_variables b bi bj)) (sudoku_π sol₂)
    rw [alldifferent_holds_iff]
    unfold box_variables
    simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
    show (List.ofFn fun k : Fin (b * b) =>
        sudoku_π sol₂ (boxCellIndex b bi bj
          ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
          ⟨k.val % b, Nat.mod_lt k.val h_b⟩)).Nodup
    exact sudoku_forward_box_alldifferent h_b sol₂ h_sol₂ bi bj

end Forward

/-! ### Backward Direction: Compact → Expanded -/

section Backward

variable {b : ℕ} (h_b : 0 < b)
include h_b

/-- Backward: box-value sum = 1.
    Box alldiff + bounds [0,n-1] → injective on Fin n → bijective → each value once -/
lemma sudoku_backward_box_value (a : IntAssignment (gridSize b * gridSize b))
    (h_sol : IntCSP.isSolutionInt (sudoku_csp b) a)
    (bi bj : Fin b) (v : Fin (gridSize b)) :
    (List.ofFn fun k : Fin (b * b) =>
      sudoku_lift (gridSize_pos h_b) a (ls_cellIndex (gridSize b)
        (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                               ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v)).sum = 1 := by
  -- Expand lift definitions
  have h_n := gridSize_pos h_b
  have h_term : ∀ k : Fin (b * b), sudoku_lift h_n a (ls_cellIndex (gridSize b)
      (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                             ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v) =
      if a (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                                   ⟨k.val % b, Nat.mod_lt k.val h_b⟩) = v.val then (1 : ℤ) else 0 := by
    intro k
    unfold sudoku_lift ls_lift
    have h_div := ls_cellIndex_div
      (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                             ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v
    have h_mod := ls_cellIndex_mod
      (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                             ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v
    simp only [h_mod]
    let di : Fin b := ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
    let dj : Fin b := ⟨k.val % b, Nat.mod_lt k.val h_b⟩
    let cell := boxCellIndex b bi bj di dj
    let idx := ls_cellIndex (gridSize b) cell v
    have h_cell_fin : (⟨idx.val / (gridSize b), by
      rw [Nat.div_lt_iff_lt_mul h_n]; exact idx.isLt⟩ : Fin (gridSize b * gridSize b)) =
      cell := by ext; exact h_div
    rw [h_cell_fin]
  simp only [h_term]
  -- Box alldiff gives injectivity
  have h_box_nodup : (List.ofFn fun k => a ((box_variables b bi bj).get k)).Nodup := by
    have h_mem : alldifferent (box_variables b bi bj) ∈ (sudoku_csp b).constraints := by
      unfold sudoku_csp box_constraints
      simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
      right
      exact ⟨bi, bj, rfl⟩
    have h_sat := (alldifferent_holds_iff _ _).mp (h_sol (alldifferent (box_variables b bi bj)) h_mem)
    -- h_sat : (box_variables b bi bj).toList.map a is Nodup
    -- convert to .get form
    have h_eq : (box_variables b bi bj).toList.map a =
        List.ofFn fun k => a ((box_variables b bi bj).get k) := by
      apply List.ext_getElem
      · simp
      · intro i h1 h2
        simp [_root_.Vector.get]
    rw [← h_eq]
    exact h_sat
  have h_box_eq : (fun k : Fin (b * b) => a ((box_variables b bi bj).get k)) =
                  (fun k : Fin (b * b) => a (boxCellIndex b bi bj
                    ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                    ⟨k.val % b, Nat.mod_lt k.val h_b⟩)) := by
    funext k
    simp [box_variables, _root_.Vector.get, _root_.Vector.ofFn]
  rw [h_box_eq] at h_box_nodup
  have h_inj : Function.Injective (fun k : Fin (b * b) => a (boxCellIndex b bi bj
      ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
      ⟨k.val % b, Nat.mod_lt k.val h_b⟩)) :=
    (List.nodup_ofFn).mp h_box_nodup
  -- Bounds
  have h_ls_sol := sudoku_sol_is_ls_sol a h_sol
  have h_bounds : ∀ k : Fin (b * b), 0 ≤ a (boxCellIndex b bi bj
      ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
      ⟨k.val % b, Nat.mod_lt k.val h_b⟩) ∧
    a (boxCellIndex b bi bj
      ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
      ⟨k.val % b, Nat.mod_lt k.val h_b⟩) < gridSize b := by
    intro k
    exact ls_compact_bounds a h_ls_sol _
  -- Define f : Fin(b²) → Fin(b²) via assignment
  let f : Fin (b * b) → Fin (b * b) := fun k =>
    ⟨(a (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                               ⟨k.val % b, Nat.mod_lt k.val h_b⟩)).toNat, by
      exact (Int.toNat_lt (h_bounds k).1).mpr (h_bounds k).2⟩
  have h_f_inj : Function.Injective f := by
    intro k₁ k₂ h_eq
    have h_val_eq : (a (boxCellIndex b bi bj ⟨k₁.val / b, Nat.div_lt_of_lt_mul k₁.isLt⟩
        ⟨k₁.val % b, Nat.mod_lt k₁.val h_b⟩)).toNat =
                    (a (boxCellIndex b bi bj ⟨k₂.val / b, Nat.div_lt_of_lt_mul k₂.isLt⟩
        ⟨k₂.val % b, Nat.mod_lt k₂.val h_b⟩)).toNat :=
      Fin.val_eq_of_eq h_eq
    have h_int_eq : a (boxCellIndex b bi bj ⟨k₁.val / b, Nat.div_lt_of_lt_mul k₁.isLt⟩
        ⟨k₁.val % b, Nat.mod_lt k₁.val h_b⟩) =
                    a (boxCellIndex b bi bj ⟨k₂.val / b, Nat.div_lt_of_lt_mul k₂.isLt⟩
        ⟨k₂.val % b, Nat.mod_lt k₂.val h_b⟩) := by
      have h1 := Int.toNat_of_nonneg (h_bounds k₁).1
      have h2 := Int.toNat_of_nonneg (h_bounds k₂).1
      rw [← h1, ← h2, h_val_eq]
    exact h_inj h_int_eq
  have h_f_surj : Function.Surjective f := by
    haveI : Finite (Fin (b * b)) := Finite.intro (Equiv.refl _)
    exact Finite.surjective_of_injective h_f_inj
  obtain ⟨k₀, hk₀⟩ := h_f_surj v
  have h_k₀_eq : a (boxCellIndex b bi bj ⟨k₀.val / b, Nat.div_lt_of_lt_mul k₀.isLt⟩
                                          ⟨k₀.val % b, Nat.mod_lt k₀.val h_b⟩) = v.val := by
    have h_simp := congr_arg Fin.val hk₀
    simp [f] at h_simp
    have h_nonneg := Int.toNat_of_nonneg (h_bounds k₀).1
    rw [← h_nonneg, h_simp]
  have h_others : ∀ k : Fin (b * b), k ≠ k₀ →
      a (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                               ⟨k.val % b, Nat.mod_lt k.val h_b⟩) ≠ v.val := by
    intro k h_ne h_eq
    have h_k_eq : f k = v := by
      apply Fin.ext; simp [f]
      have h_nonneg := Int.toNat_of_nonneg (h_bounds k).1
      exact_mod_cast h_nonneg.trans h_eq
    have h_k₀_eq' : f k₀ = v := hk₀
    exact h_ne (h_f_inj (h_k_eq.trans h_k₀_eq'.symm))
  -- Sum = 1
  trans ((List.ofFn fun k : Fin (b * b) => if k = k₀ then (1 : ℤ) else 0).sum)
  · congr 1; congr 1
    funext k
    by_cases h : a (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩ ⟨k.val % b, Nat.mod_lt k.val h_b⟩) = ↑v.val
    · have : k = k₀ := by by_contra h_ne; exact h_others k h_ne h
      rw [if_pos h, if_pos this]
    · have : k ≠ k₀ := by intro h_eq; rw [h_eq] at h; exact h h_k₀_eq
      rw [if_neg h, if_neg this]
  · rw [List.ofFn_eq_map, ← List.sum_toFinset _ (List.nodup_finRange (b * b)),
        List.toFinset_finRange, Finset.sum_eq_single k₀]
    · simp
    · intro k _ h_ne; simp [h_ne]
    · intro h_mem; exfalso; exact h_mem (Finset.mem_univ k₀)

/-- Backward direction: sudoku compact solution → sudoku matrix solution -/
theorem sudoku_backward (sol₁ : IntAssignment (gridSize b * gridSize b))
    (h_sol₁ : IntCSP.isSolutionInt (sudoku_csp b) sol₁) :
    ∃ sol₂ : IntAssignment (gridSize b * gridSize b * gridSize b),
      IntCSP.isSolutionInt (sudoku_matrix b) sol₂ ∧
      sudoku_π sol₂ = sol₁ := by
  have h_n := gridSize_pos h_b
  let sol₂ := sudoku_lift h_n sol₁
  use sol₂
  constructor
  · -- sol₂ satisfies sudoku_matrix
    have h_ls_sol := sudoku_sol_is_ls_sol sol₁ h_sol₁
    have h_ls_matrix := ls_lift_satisfies_matrix sol₁ h_n h_ls_sol
    unfold IntCSP.isSolutionInt
    intro tc h_tc
    unfold sudoku_matrix at h_tc
    simp only [List.mem_append] at h_tc
    rcases h_tc with (((h1 | h2) | h3) | h4) | h5
    · -- Binary bounds: delegate to LS matrix
      exact h_ls_matrix tc (by
        unfold latin_square_matrix
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ h1)))
    · -- Cell one-hot
      exact h_ls_matrix tc (by
        unfold latin_square_matrix
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h2)))
    · -- Row-value
      exact h_ls_matrix tc (by
        unfold latin_square_matrix
        exact List.mem_append_left _ (List.mem_append_right _ h3))
    · -- Col-value
      exact h_ls_matrix tc (by
        unfold latin_square_matrix
        exact List.mem_append_right _ h4)
    · -- Box-value constraints (NEW)
      unfold sudoku_box_value_constraints at h5
      simp only [List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at h5
      obtain ⟨bi, bj, v, rfl⟩ := h5
      show IntCSP.satisfiesConstraintInt (sum_eq (sudoku_box_value_vars b bi bj v) 1) sol₂
      rw [sum_eq_holds_iff]
      unfold sudoku_box_value_vars
      simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
      show (List.ofFn fun k : Fin (b * b) =>
          sol₂ (ls_cellIndex (gridSize b)
            (boxCellIndex b bi bj ⟨k.val / b, Nat.div_lt_of_lt_mul k.isLt⟩
                                   ⟨k.val % b, Nat.mod_lt k.val h_b⟩) v)).sum = 1
      exact sudoku_backward_box_value h_b sol₁ h_sol₁ bi bj v
  · -- π∘lift = id
    show sudoku_π (sudoku_lift h_n sol₁) = sol₁
    unfold sudoku_π sudoku_lift
    have h_bounds : ∀ c : Fin (gridSize b * gridSize b), 0 ≤ sol₁ c ∧ sol₁ c < gridSize b := by
      intro c
      exact ls_compact_bounds sol₁ (sudoku_sol_is_ls_sol sol₁ h_sol₁) c
    exact ls_π_lift_inverse h_n sol₁ h_bounds

end Backward

/-! ### Injectivity (direct from Latin Square) -/

section Injectivity

variable {b : ℕ} (h_b : 0 < b)
include h_b

/-- Injectivity: same as Latin Square (only depends on cell one-hot + binary bounds) -/
theorem sudoku_injective (sol₂ sol₂' : IntAssignment (gridSize b * gridSize b * gridSize b))
    (h_sol₂ : IntCSP.isSolutionInt (sudoku_matrix b) sol₂)
    (h_sol₂' : IntCSP.isSolutionInt (sudoku_matrix b) sol₂')
    (h_proj_eq : sudoku_π sol₂ = sudoku_π sol₂') :
    sol₂ = sol₂' := by
  unfold sudoku_π at h_proj_eq
  exact ls_injective sol₂ sol₂' (gridSize_pos h_b)
    (sudoku_matrix_sol_is_ls_sol sol₂ h_sol₂)
    (sudoku_matrix_sol_is_ls_sol sol₂' h_sol₂')
    h_proj_eq

end Injectivity

/-! ### Main Theorems -/

/-- Sudoku formulations are π-equivalent -/
theorem sudoku_pi_equivalent (b : ℕ) (h_b : 0 < b) :
    piEquivalent
      (sudoku_csp b)
      (sudoku_matrix b)
      (@sudoku_π b) := by
  constructor
  · exact sudoku_forward h_b
  constructor
  · exact fun sol₁ h_sol₁ => sudoku_backward h_b sol₁ h_sol₁
  · exact fun sol₂ sol₂' h₁ h₂ h₃ => sudoku_injective h_b sol₂ sol₂' h₁ h₂ h₃

/-- Derived: Full equivalence -/
theorem sudoku_formulations_equivalent (b : ℕ) (h_b : 0 < b) :
    equivalent
      (sudoku_matrix b)
      (sudoku_csp b) := by
  apply piEquivalent_implies_equivalent
  exact sudoku_pi_equivalent b h_b

/-- Derived: Equisatisfiability -/
theorem sudoku_equisatisfiable (b : ℕ) (h_b : 0 < b) :
    equisatisfiable
      (sudoku_csp b)
      (sudoku_matrix b) := by
  apply piEquivalent_implies_equisatisfiable
  exact sudoku_pi_equivalent b h_b

end Sudoku
