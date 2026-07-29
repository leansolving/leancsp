import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Translate
import CSP.L2S.Proofs.PatternBridges
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith

open CSP.L2S

/-!
## Latin Square

Variables: One per cell (n*n)
Domains: 0..(n-1)
Constraints: No repeated values per row/column
-/

/-! ### Local pattern-satisfaction helpers (port to `patternHolds` semantics) -/

/-- Local port helper: a vector scope mapped through an assignment equals the
    `List.ofFn`/`Vector.get` form this file's index arithmetic is phrased in. -/
private lemma toList_map_eq_ofFn_get {N k : ℕ} (vec : _root_.Vector (VarType N) k)
    (a : IntAssignment N) :
    vec.toList.map a = List.ofFn fun j => a (vec.get j) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [_root_.Vector.get]

/-- Local port helper: `alldifferent` over a vector scope, values in `.get` form. -/
private lemma alldifferent_get_holds_iff {N k : ℕ} (vec : _root_.Vector (VarType N) k)
    (a : IntAssignment N) :
    IntCSP.satisfiesConstraintInt (alldifferent vec) a ↔
    (List.ofFn fun j => a (vec.get j)).Nodup := by
  rw [alldifferent_holds_iff, toList_map_eq_ofFn_get]

/-- Local port helper: `increasing` over a vector scope, values in `.get` form. -/
private lemma increasing_get_holds_iff {N k : ℕ} (vec : _root_.Vector (VarType N) k)
    (a : IntAssignment N) :
    IntCSP.satisfiesConstraintInt (increasing vec) a ↔
    List.Pairwise (· ≤ ·) (List.ofFn fun j => a (vec.get j)) := by
  rw [increasing_holds_iff, toList_map_eq_ofFn_get]

/-! ### CSP Definition -/

/- Bound constraints -/
def bound_constraints (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.finRange (n*n)).map (fun v => bound v 0 (n-1))

/- Helper function: get all variables in a row -/
def row_variables (i : Fin n) : Vector (VarType (n*n)) n :=
  Vector.ofFn (fun j => ⟨i.val * n + j.val, by
    have h1 : i.val < n := i.isLt
    have h2 : j.val < n := j.isLt
    calc i.val * n + j.val
        < i.val * n + n := Nat.add_lt_add_left h2 _
      _ = (i.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩)

/- Helper function: get all variables in a column -/
def col_variables (j : Fin n) : Vector (VarType (n*n)) n :=
  Vector.ofFn (fun i => ⟨i.val * n + j.val, by
    have h1 : i.val < n := i.isLt
    have h2 : j.val < n := j.isLt
    calc i.val * n + j.val
        < i.val * n + n := Nat.add_lt_add_left h2 _
      _ = (i.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩)

/- Row constraints -/
def row_constraints (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.finRange n).map (fun r => alldifferent (row_variables r))

/- Column constraints -/
def col_constraints (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.finRange n).map (fun c => alldifferent (col_variables c))

/- CSP Definition -/
def latin_square_csp (n : ℕ) : IntCSP :=
  ⟨ n*n,
    bound_constraints n ++
    row_constraints n ++
    col_constraints n ⟩

/-! ### Column Permutation Symmetry -/

/-- Column permutation: applies permutation σ to column indices.
    A cell at position (i, j) with index k = i*n + j
    maps to position (i, σ(j)) with index i*n + σ(j). -/
def column_permutation (n : ℕ) (h_n : 0 < n) (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm (VarType (n*n)) where
  toFun := fun v =>
    let i := v.val / n  -- row index
    let j := v.val % n  -- column index
    let j_fin : Fin n := ⟨j, Nat.mod_lt v.val h_n⟩
    let σj := σ j_fin
    ⟨i * n + σj.val, by
      have h_i : i < n := Nat.div_lt_iff_lt_mul h_n |>.mpr v.isLt
      have h_σj : σj.val < n := σj.isLt
      calc i * n + σj.val
          < i * n + n := Nat.add_lt_add_left h_σj (i * n)
        _ = (i + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h_i)⟩
  invFun := fun v =>
    let i := v.val / n
    let j := v.val % n
    let j_fin : Fin n := ⟨j, Nat.mod_lt v.val h_n⟩
    let σ_inv_j := σ.symm j_fin
    ⟨i * n + σ_inv_j.val, by
      have h_i : i < n := Nat.div_lt_iff_lt_mul h_n |>.mpr v.isLt
      have h_σ_inv_j : σ_inv_j.val < n := σ_inv_j.isLt
      calc i * n + σ_inv_j.val
          < i * n + n := Nat.add_lt_add_left h_σ_inv_j (i * n)
        _ = (i + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h_i)⟩
  left_inv := by
    intro v
    ext
    simp only []
    -- Extract row and column from v
    have h_i_lt : v.val / n < n := Nat.div_lt_iff_lt_mul h_n |>.mpr v.isLt
    have h_j_lt : v.val % n < n := Nat.mod_lt v.val h_n

    set i := v.val / n
    set j := v.val % n
    set σj := (σ ⟨j, h_j_lt⟩).val

    -- Key facts
    have h_σj_lt : σj < n := (σ ⟨j, h_j_lt⟩).isLt

    -- Division: (i*n + σj) / n = i
    have h_div : (i * n + σj) / n = i := by
      have h1 : σj / n = 0 := Nat.div_eq_of_lt h_σj_lt
      calc (i * n + σj) / n
          = (σj + n * i) / n := by rw [Nat.mul_comm i n]; ring_nf
        _ = σj / n + i := Nat.add_mul_div_left σj i h_n
        _ = 0 + i := by rw [h1]
        _ = i := Nat.zero_add i

    -- Modulo: (i*n + σj) % n = σj
    have h_mod : (i * n + σj) % n = σj := by
      have h1 : σj % n = σj := Nat.mod_eq_of_lt h_σj_lt
      calc (i * n + σj) % n
          = (n * i + σj) % n := by rw [Nat.mul_comm i n]
        _ = σj % n := Nat.mul_add_mod_self_left n i σj
        _ = σj := h1

    have h_inv_perm : σ.symm (σ ⟨j, h_j_lt⟩) = ⟨j, h_j_lt⟩ := Equiv.symm_apply_apply σ _

    -- Show the computed value equals v.val
    calc (i * n + σj) / n * n + (σ.symm ⟨(i * n + σj) % n, Nat.mod_lt _ h_n⟩).val
        = i * n + (σ.symm ⟨(i * n + σj) % n, Nat.mod_lt _ h_n⟩).val := by
            rw [h_div]
      _ = i * n + (σ.symm ⟨σj, h_σj_lt⟩).val := by
            congr 1
            have h_fin_eq : (⟨(i * n + σj) % n, Nat.mod_lt _ h_n⟩ : Fin n) = ⟨σj, h_σj_lt⟩ := by
              exact Fin.ext h_mod
            rw [h_fin_eq]
      _ = i * n + (σ.symm (σ ⟨j, h_j_lt⟩)).val := by
            have : σ.symm ⟨σj, h_σj_lt⟩ = σ.symm (σ ⟨j, h_j_lt⟩) := by
              congr
            rw [this]
      _ = i * n + (⟨j, h_j_lt⟩ : Fin n).val := by
            rw [h_inv_perm]
      _ = i * n + j := rfl
      _ = v.val := by
            have h_eq := Nat.div_add_mod v.val n
            calc i * n + j
                = v.val / n * n + v.val % n := by rfl
              _ = n * (v.val / n) + v.val % n := by rw [Nat.mul_comm]
              _ = v.val := h_eq

  right_inv := by
    intro v
    ext
    simp only []
    -- Extract row and column from v
    have h_i_lt : v.val / n < n := Nat.div_lt_iff_lt_mul h_n |>.mpr v.isLt
    have h_j_lt : v.val % n < n := Nat.mod_lt v.val h_n

    set i := v.val / n
    set j := v.val % n
    set σinvj := (σ.symm ⟨j, h_j_lt⟩).val

    -- Key facts
    have h_σinvj_lt : σinvj < n := (σ.symm ⟨j, h_j_lt⟩).isLt

    -- Division: (i*n + σinvj) / n = i
    have h_div : (i * n + σinvj) / n = i := by
      have h1 : σinvj / n = 0 := Nat.div_eq_of_lt h_σinvj_lt
      calc (i * n + σinvj) / n
          = (σinvj + n * i) / n := by rw [Nat.mul_comm i n]; ring_nf
        _ = σinvj / n + i := Nat.add_mul_div_left σinvj i h_n
        _ = 0 + i := by rw [h1]
        _ = i := Nat.zero_add i

    -- Modulo: (i*n + σinvj) % n = σinvj
    have h_mod : (i * n + σinvj) % n = σinvj := by
      have h1 : σinvj % n = σinvj := Nat.mod_eq_of_lt h_σinvj_lt
      calc (i * n + σinvj) % n
          = (n * i + σinvj) % n := by rw [Nat.mul_comm i n]
        _ = σinvj % n := Nat.mul_add_mod_self_left n i σinvj
        _ = σinvj := h1

    have h_inv_perm : σ (σ.symm ⟨j, h_j_lt⟩) = ⟨j, h_j_lt⟩ := Equiv.apply_symm_apply σ _

    -- Show the computed value equals v.val
    calc (i * n + σinvj) / n * n + (σ ⟨(i * n + σinvj) % n, Nat.mod_lt _ h_n⟩).val
        = i * n + (σ ⟨(i * n + σinvj) % n, Nat.mod_lt _ h_n⟩).val := by
            rw [h_div]
      _ = i * n + (σ ⟨σinvj, h_σinvj_lt⟩).val := by
            congr 1
            have h_fin_eq : (⟨(i * n + σinvj) % n, Nat.mod_lt _ h_n⟩ : Fin n) = ⟨σinvj, h_σinvj_lt⟩ := by
              exact Fin.ext h_mod
            rw [h_fin_eq]
      _ = i * n + (σ (σ.symm ⟨j, h_j_lt⟩)).val := by
            have : σ ⟨σinvj, h_σinvj_lt⟩ = σ (σ.symm ⟨j, h_j_lt⟩) := by
              congr
            rw [this]
      _ = i * n + (⟨j, h_j_lt⟩ : Fin n).val := by
            rw [h_inv_perm]
      _ = i * n + j := rfl
      _ = v.val := by
            have h_eq := Nat.div_add_mod v.val n
            calc i * n + j
                = v.val / n * n + v.val % n := by rfl
              _ = n * (v.val / n) + v.val % n := by rw [Nat.mul_comm]
              _ = v.val := h_eq

/-- Construct sorting permutation for first row.
    Given the values in the first row, construct a permutation σ such that
    the values are sorted when read in order σ(0), σ(1), ..., σ(n-1). -/
def sorting_permutation (n : ℕ) (first_row : Fin n → ℤ) : Equiv.Perm (Fin n) :=
  Tuple.sort first_row

/-! ### Symmetry Breaking Constraint Definition -/

/- Symmetry breaking constraint: first row must be in non-decreasing order.
   Uses the new `increasing` constraint. -/
def latin_square_sbc (n : ℕ) (h_n : 0 < n) : IntConstraint (n*n) :=
  increasing (row_variables ⟨0, h_n⟩)

/- Extended CSP (including the SBC) -/
def latin_square_sb (n : ℕ) (h_n : 0 < n) : IntCSP :=
  (latin_square_csp n).addConstraint (latin_square_sbc n h_n)

/-! ### Symmetry-Breaking Correctness -/

/-- Helper lemma: column_permutation only changes the column index -/
lemma column_permutation_structure (n : ℕ) (h_n : 0 < n) (σ : Equiv.Perm (Fin n)) (v : VarType (n*n)) :
    let i := v.val / n
    let j := v.val % n
    let j_fin : Fin n := ⟨j, Nat.mod_lt v.val h_n⟩
    let σj := σ j_fin
    (column_permutation n h_n σ v).val = i * n + σj.val := by
  simp only [column_permutation]
  rfl

/-- Result 1: Column permutation is a variable symmetry for Latin Squares -/
theorem column_permutation_is_variable_symmetry (n : ℕ) (h_n : 0 < n) (σ : Equiv.Perm (Fin n)) :
    VariableSymmetry (latin_square_csp n) (column_permutation n h_n σ) := by
  unfold VariableSymmetry IntCSP.isSolutionInt
  intro assignment h_sol tc h_tc_mem
  unfold latin_square_csp at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  rcases h_tc_mem with (h_bound | h_row) | h_col
  · unfold bound_constraints at h_bound
    simp only [List.mem_map, List.mem_finRange] at h_bound
    obtain ⟨v, _, rfl⟩ := h_bound
    let βv := column_permutation n h_n σ v
    have h_βv_bound : bound βv 0 (n-1) ∈ (latin_square_csp n).constraints := by
      unfold latin_square_csp bound_constraints
      simp only [List.mem_append, List.mem_map, List.mem_finRange]
      left; left
      exact ⟨βv, trivial, rfl⟩
    have h_βv_sat := h_sol (bound βv 0 (n-1)) h_βv_bound
    rw [bound_holds_iff] at h_βv_sat
    exact (bound_holds_iff _ _ _ _).mpr h_βv_sat
  · unfold row_constraints at h_row
    simp only [List.mem_map, List.mem_finRange] at h_row
    obtain ⟨r, _, rfl⟩ := h_row
    refine (alldifferent_get_holds_iff (row_variables r) _).mpr ?_
    have h_orig : (List.ofFn fun j => assignment ((row_variables r).get j)).Nodup := by
      have h_mem : alldifferent (row_variables r) ∈ (latin_square_csp n).constraints := by
        unfold latin_square_csp row_constraints
        simp only [List.mem_append, List.mem_map, List.mem_finRange]
        left; right
        exact ⟨r, trivial, rfl⟩
      have := h_sol (alldifferent (row_variables r)) h_mem
      exact (alldifferent_get_holds_iff _ _).mp this
    have h_perm : (List.ofFn fun i => (assignment ∘ column_permutation n h_n σ) ((row_variables r).get i)) =
                  (List.ofFn fun i => assignment ((row_variables r).get (σ i))) := by
      congr
      ext j
      simp only [Function.comp_apply, row_variables, _root_.Vector.get, _root_.Vector.ofFn]
      have h_bound : r.val * n + j.val < n * n := by
        calc r.val * n + j.val
            < r.val * n + n := Nat.add_lt_add_left j.isLt _
          _ = n * (r.val + 1) := by ring
          _ ≤ n * n := Nat.mul_le_mul_left n (Nat.succ_le_of_lt r.isLt)
      have h_eq : (column_permutation n h_n σ ⟨r.val * n + j.val, h_bound⟩).val = r.val * n + (σ j).val := by
        simp only [column_permutation]
        have h_div : (r.val * n + j.val) / n = r.val := by
          calc (r.val * n + j.val) / n
              = (j.val + r.val * n) / n := by ring_nf
            _ = (j.val + n * r.val) / n := by rw [Nat.mul_comm]
            _ = j.val / n + r.val := Nat.add_mul_div_left j.val r.val h_n
            _ = 0 + r.val := by
              congr 1
              rw [Nat.div_eq_zero_iff]
              right
              exact j.isLt
            _ = r.val := Nat.zero_add r.val
        have h_mod : (r.val * n + j.val) % n = j.val := by
          calc (r.val * n + j.val) % n
              = (j.val + r.val * n) % n := by ring_nf
            _ = (j.val + n * r.val) % n := by rw [Nat.mul_comm]
            _ = (n * r.val + j.val) % n := by ring_nf
            _ = j.val % n := Nat.mul_add_mod_self_left n r.val j.val
            _ = j.val := Nat.mod_eq_of_lt j.isLt
        simp [h_div, h_mod]
      have h_fin_eq : (column_permutation n h_n σ ⟨r.val * n + j.val, h_bound⟩) = ⟨r.val * n + (σ j).val, by omega⟩ := Fin.ext h_eq
      simp only [Array.getElem_ofFn]
      exact congrArg assignment h_fin_eq

    show (List.ofFn fun i => (assignment ∘ column_permutation n h_n σ) ((row_variables r).get i)).Nodup
    rw [h_perm]
    have h_perm_list := Equiv.Perm.ofFn_comp_perm σ (fun i => assignment ((row_variables r).get i))
    exact (List.Perm.nodup_iff h_perm_list).mpr h_orig
  · unfold col_constraints at h_col
    simp only [List.mem_map, List.mem_finRange] at h_col
    obtain ⟨c, _, rfl⟩ := h_col
    refine (alldifferent_get_holds_iff (col_variables c) _).mpr ?_
    have h_col_perm : (List.ofFn fun i => (assignment ∘ column_permutation n h_n σ) ((col_variables c).get i)) =
                      (List.ofFn fun i => assignment ((col_variables (σ c)).get i)) := by
      congr
      ext i
      simp only [Function.comp_apply, col_variables, _root_.Vector.get, _root_.Vector.ofFn]
      have h_bound : i.val * n + c.val < n * n := by
        calc i.val * n + c.val
            < i.val * n + n := Nat.add_lt_add_left c.isLt _
          _ = n * (i.val + 1) := by ring
          _ ≤ n * n := Nat.mul_le_mul_left n (Nat.succ_le_of_lt i.isLt)
      have h_eq : (column_permutation n h_n σ ⟨i.val * n + c.val, h_bound⟩).val = i.val * n + (σ c).val := by
        simp only [column_permutation]
        have h_div : (i.val * n + c.val) / n = i.val := by
          calc (i.val * n + c.val) / n
              = (c.val + i.val * n) / n := by ring_nf
            _ = (c.val + n * i.val) / n := by rw [Nat.mul_comm]
            _ = c.val / n + i.val := Nat.add_mul_div_left c.val i.val h_n
            _ = 0 + i.val := by
              congr 1
              rw [Nat.div_eq_zero_iff]
              right
              exact c.isLt
            _ = i.val := Nat.zero_add i.val
        have h_mod : (i.val * n + c.val) % n = c.val := by
          calc (i.val * n + c.val) % n
              = (c.val + i.val * n) % n := by ring_nf
            _ = (c.val + n * i.val) % n := by rw [Nat.mul_comm]
            _ = (n * i.val + c.val) % n := by ring_nf
            _ = c.val % n := Nat.mul_add_mod_self_left n i.val c.val
            _ = c.val := Nat.mod_eq_of_lt c.isLt
        simp [h_div, h_mod]
      have h_fin_eq : (column_permutation n h_n σ ⟨i.val * n + c.val, h_bound⟩) = ⟨i.val * n + (σ c).val, by omega⟩ := Fin.ext h_eq
      simp only [Array.getElem_ofFn]
      exact congrArg assignment h_fin_eq
    show (List.ofFn fun i => (assignment ∘ column_permutation n h_n σ) ((col_variables c).get i)).Nodup
    rw [h_col_perm]
    have h_mem : alldifferent (col_variables (σ c)) ∈ (latin_square_csp n).constraints := by
      unfold latin_square_csp col_constraints
      simp only [List.mem_append, List.mem_map, List.mem_finRange]
      right
      exact ⟨σ c, trivial, rfl⟩
    have := h_sol (alldifferent (col_variables (σ c))) h_mem
    exact (alldifferent_get_holds_iff _ _).mp this

/-- Result 2: The symmetry breaking constraint is a variable symmetry breaking constraint -/
theorem latin_square_sbc_is_variable_symmetry_breaking (n : ℕ) (h_n : 0 < n) :
    variableSymmetryBreakingConstraint
      (latin_square_csp n)
      (latin_square_sbc n h_n) := by
  unfold variableSymmetryBreakingConstraint
  intro assignment h_sol

  let first_row := fun j : Fin n => assignment ((row_variables ⟨0, h_n⟩).get j)
  let σ := sorting_permutation n first_row

  use column_permutation n h_n σ

  constructor
  · exact column_permutation_is_variable_symmetry n h_n σ

  · intro tc h_tc_mem
    simp only [IntCSP.addConstraint] at h_tc_mem
    obtain h_sbc | h_orig := List.mem_cons.mp h_tc_mem
    · rw [h_sbc]
      unfold latin_square_sbc
      refine (increasing_get_holds_iff (row_variables ⟨0, h_n⟩) _).mpr ?_

      have h_mono : Monotone (first_row ∘ σ) := by
        unfold sorting_permutation at σ
        exact Tuple.monotone_sort first_row

      rw [← List.sortedLE_iff_pairwise, List.sortedLE_ofFn_iff]

      intro i1 i2 h_le
      simp only [Function.comp_apply]
      -- Lean 4.30 core `Vector`: reduce `.get` of `ofFn` directly.  The old
      -- `Vector.get`→`Array.getElem` simp path no longer normalises in context.
      have vget : ∀ {α : Type} {m : ℕ} (f : Fin m → α) (k : Fin m),
          (Vector.ofFn f).get k = f k := by
        intro α m f k
        simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn, Fin.val_cast, Fin.eta]
      -- The column permutation sends the row-0 variable for column k to that for σ k.
      have hperm : ∀ (k : Fin n),
          column_permutation n h_n σ ((row_variables ⟨0, h_n⟩).get k)
            = (row_variables ⟨0, h_n⟩).get (σ k) := by
        intro k
        apply Fin.ext
        simp [column_permutation, row_variables, vget, Nat.div_eq_of_lt, Nat.mod_eq_of_lt]
      calc assignment (column_permutation n h_n σ ((row_variables ⟨0, h_n⟩).get i1))
          = assignment ((row_variables ⟨0, h_n⟩).get (σ i1)) := by rw [hperm i1]
        _ = first_row (σ i1) := rfl
        _ ≤ first_row (σ i2) := by simpa [Function.comp_apply] using h_mono h_le
        _ = assignment ((row_variables ⟨0, h_n⟩).get (σ i2)) := rfl
        _ = assignment (column_permutation n h_n σ ((row_variables ⟨0, h_n⟩).get i2)) := by
              rw [hperm i2]

    · have h_sym := column_permutation_is_variable_symmetry n h_n σ
      unfold VariableSymmetry at h_sym
      have h_sol_orig := h_sym assignment h_sol
      exact h_sol_orig tc h_orig

/-- Result 3: General symmetry breaking constraint -/
theorem latin_square_sbc_is_symmetry_breaking (n : ℕ) (h_n : 0 < n) :
    symmetryBreakingConstraint
      (latin_square_csp n)
      (latin_square_sbc n h_n) := by
  unfold symmetryBreakingConstraint
  right  -- Choose variable symmetry breaking
  exact latin_square_sbc_is_variable_symmetry_breaking n h_n

/-- Result 4: Equisatisfiability -/
theorem latin_square_equisatisfiability (n : ℕ) (h_n : 0 < n) :
    equisatisfiable
      (latin_square_csp n)
      (latin_square_sb n h_n) := by
  apply variableSymmetryBreaking_equisatisfiability
  exact latin_square_sbc_is_variable_symmetry_breaking n h_n

/-! ### Solver translation -/

def main : IO Unit := do
  let lb := 10
  let ub := 50
  let step := 5
  let count := ((ub - lb) / step) + 1
  let sizes := (List.range count).map (fun i => lb + i * step)

  IO.println s!"Generating Latin Square instances (BASE and +SBC) for n={lb} to n={ub}..."

  for n in sizes do
    if h_n : 0 < n then
      IO.println s!"  Generating n={n}..."

      let base_csp := latin_square_csp n
      let sbc_csp := latin_square_sb n h_n

      -- Generate base instances
      saveToAuto base_csp s!"CSP/L2S/Proofs/mzn/latin_square/base_{n}" BackendType.MiniZinc
      saveToAuto base_csp s!"CSP/L2S/Proofs/smt2/latin_square/base_{n}" BackendType.SMTLIB

      -- Generate SBC instances
      saveToAuto sbc_csp s!"CSP/L2S/Proofs/mzn/latin_square/sbc_{n}" BackendType.MiniZinc
      saveToAuto sbc_csp s!"CSP/L2S/Proofs/smt2/latin_square/sbc_{n}" BackendType.SMTLIB
    else
      IO.println s!"  Skipping n={n}"

  IO.println s!"✓ Generated Latin Square instances for n={lb} to n={ub}"
