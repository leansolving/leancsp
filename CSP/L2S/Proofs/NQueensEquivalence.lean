import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Translate
import CSP.L2S.Proofs.PatternBridges
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.OfFn

open CSP.L2S CSP.L2S.PB

/-!
## N-Queens equivalent problems

### Formulation 1
Variables: One per column (n)
Domains: Rows of the corresponding queens
Constraints: Different queens must be in different rows, columns and diagonals

### Formulation 2
Variables: One per square (n^2)
Domain: 1 if there is a queen on square i,j; 0 otherwise
Constraints: Different queens must be in different rows, columns and diagonals

-/

-- ============================================================================
-- CSP definitions
-- ============================================================================

-- Formulation 1

/- Bounds: from 0 to n-1 -/
def bound_constraints1D (n : ℕ) : List (IntConstraint n) :=
  (List.finRange n).map (fun v => bound v 0 (n-1))

/- All queens must be placed in different rows -/
def row_constraint1D (n : ℕ) : IntConstraint n :=
  alldifferent_all n

/- All queens must be placed in different diagonals (x[i] - i all different) -/
def diagonal_constraint1D (n : ℕ) : IntConstraint n :=
  alldifferent_diag_neg n

/- All queens must be placed in different antidiagonals (x[i] + i all different) -/
def antidiagonal_constraint1D (n : ℕ) : IntConstraint n :=
  alldifferent_diag_pos n

/- CSP: include all constraints -/
def nqueens_csp1D (n : ℕ) : IntCSP :=
  ⟨ n,
    bound_constraints1D n ++
    [row_constraint1D n] ++
    [diagonal_constraint1D n] ++
    [antidiagonal_constraint1D n] ⟩

-- Formulation 2

/- Helper function: get row from variable -/
def row {n : ℕ} (hn : 0 < n) (v : VarType (n*n)) : Fin n :=
  ⟨v.val % n, Nat.mod_lt v.val hn⟩

/- Helper function: get column from variable -/
def col {n : ℕ} (hn : 0 < n) (v : VarType (n*n)) : Fin n :=
  ⟨v.val / n, by rw [Nat.div_lt_iff_lt_mul hn]; exact v.isLt⟩

/- Helper function: get position (i,j) from variable v ∈ 0..(n*n - 1) -/
def position (hn : 0 < n) (v : VarType (n*n)) : Fin n × Fin n :=
  (row hn v, col hn v)

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

/- Helper function: get all variables in a diagonal (where row - col = d) -/
def diag_variables {n : ℕ} (d : ℤ) : List (VarType (n*n)) :=
  (List.finRange (n*n)).filter fun v =>
    ((v.val / n : ℤ) - (v.val % n : ℤ)) = d

/- Helper function: get all variables in an antidiagonal (where row + col = a) -/
def antidiag_variables {n : ℕ} (a : ℤ) : List (VarType (n*n)) :=
  (List.finRange (n*n)).filter fun v =>
    ((v.val / n : ℤ) + (v.val % n : ℤ)) = a

/- Bounds: from 0 to 1 -/
def bound_constraints2D (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.finRange (n*n)).map (fun v => bound v 0 1)

/- All queens must be placed in different rows: exactly 1 queen per row -/
def row_constraints2D (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.finRange n).map (fun i => sum_eq (row_variables i) 1)

/- All queens must be placed in different columns: exactly 1 queen per column -/
def col_constraints2D (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.finRange n).map (fun j => sum_eq (col_variables j) 1)

/- Helper: convert list to vector with length proof -/
private def listToVector {α : Type*} (l : List α) : _root_.Vector α l.length :=
  ⟨l.toArray, by simp [List.size_toArray]⟩

/- All diagonals: at most 1 queen per diagonal -/
def diag_constraints2D (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.range (2*n - 1)).filterMap fun k =>
    let d := (k : ℤ) - (n - 1)  -- offset from -(n-1) to (n-1)
    let cells := diag_variables d
    match cells with
    | [] => none
    | _ => some (sum_le (listToVector cells) 1)

/- All antidiagonals: at most 1 queen per antidiagonal -/
def antidiag_constraints2D (n : ℕ) : List (IntConstraint (n*n)) :=
  (List.range (2*n - 1)).filterMap fun k =>
    let cells := antidiag_variables k
    match cells with
    | [] => none
    | _ => some (sum_le (listToVector cells) 1)

/- CSP: include all constraints -/
def nqueens_csp2D (n : ℕ) : IntCSP :=
  ⟨ n*n,
    bound_constraints2D n ++
    row_constraints2D n  ++
    col_constraints2D n  ++
    diag_constraints2D n  ++
    antidiag_constraints2D n ⟩

-- ============================================================================
-- Equivalence Functions (Projection and Lifting)
-- ============================================================================

/--
Projection π: 2D board → 1D permutation
For each column c, find the unique row r where x(r*n + c) = 1
-/
def π {n : ℕ} (x : IntAssignment (n*n)) : IntAssignment n :=
  fun c : Fin n =>
    match (List.finRange n).find? (fun r =>
      x ⟨r.val * n + c.val, by
        have h1 : r.val < n := r.isLt
        have h2 : c.val < n := c.isLt
        calc r.val * n + c.val
            < r.val * n + n := Nat.add_lt_add_left h2 _
          _ = (r.val + 1) * n := by ring
          _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩ = 1) with
    | some r => r.val
    | none => 0  -- default value (won't occur for valid solutions)

/--
Lifting lift: 1D permutation → 2D board
Set x(r*n + c) = 1 if and only if q(c) = r
-/
def lift {n : ℕ} (hn : 0 < n) (q : IntAssignment n) : IntAssignment (n*n) :=
  fun v : Fin (n*n) =>
    let r : ℤ := v.val / n
    let c : Fin n := ⟨v.val % n, Nat.mod_lt v.val hn⟩
    if q c = r then 1 else 0

-- ============================================================================
-- Auxiliary Lemmas
-- ============================================================================

section AuxiliaryLemmas

variable {n : ℕ} (hn : 0 < n)

/-- Helper: Variable index for cell (r, c) -/
def varIndex (r c : Fin n) : Fin (n*n) :=
  ⟨r.val * n + c.val, by
    have h1 : r.val < n := r.isLt
    have h2 : c.val < n := c.isLt
    calc r.val * n + c.val
        < r.val * n + n := Nat.add_lt_add_left h2 _
      _ = (r.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩

/-- The π-lift composition is identity (when q has valid bounds) -/
lemma π_lift_inverse (q : IntAssignment n)
    (h_bounds : ∀ c : Fin n, 0 ≤ q c ∧ q c < n) :
    π (lift hn q) = q := by
  funext c
  unfold π
  have h_c := h_bounds c
  have h_toNat_eq : ((q c).toNat : ℤ) = q c := by
    have h_nonneg : 0 ≤ q c := h_c.1
    exact Int.toNat_of_nonneg h_nonneg
  let r_target : Fin n := ⟨(q c).toNat, by
    have : q c < n := h_c.2
    have : q c ≤ n - 1 := by exact Int.le_sub_one_of_lt this
    have h_nonneg : 0 ≤ q c := h_c.1
    (expose_names; exact (Int.toNat_lt h_nonneg).mpr this_1)
    ⟩
  have h_find : (List.finRange n).find? (fun r =>
      (lift hn q) ⟨r.val * n + c.val, by
        have h1 : r.val < n := r.isLt
        have h2 : c.val < n := c.isLt
        calc r.val * n + c.val
            < r.val * n + n := Nat.add_lt_add_left h2 _
          _ = (r.val + 1) * n := by ring
          _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩ = 1) = some r_target := by
    have h_eq : List.finRange n = List.ofFn id := rfl
    rw [h_eq]
    have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin n) n id
      (fun r => decide ((lift hn q) ⟨r.val * n + c.val, by
        have h1 : r.val < n := r.isLt
        have h2 : c.val < n := c.isLt
        calc r.val * n + c.val
            < r.val * n + n := Nat.add_lt_add_left h2 _
          _ = (r.val + 1) * n := by ring
          _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩ = 1))
      r_target Function.injective_id
    simp only [id_eq] at h_lem
    rw [h_lem]
    constructor
    · simp only [decide_eq_true_eq]
      unfold lift
      have h_c_mod : c.val % n = c.val := Nat.mod_eq_of_lt c.isLt
      have h_mod : (r_target.val * n + c.val) % n = c.val := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left]
        exact h_c_mod
      have h_div : (r_target.val * n + c.val) / n = r_target.val := by
        have hn_pos : 0 < n := hn
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hn_pos]
        have : c.val / n = 0 := Nat.div_eq_zero_iff.mpr (Or.inr c.isLt)
        omega
      simp only [h_mod, ite_eq_left_iff]
      intro h_ne
      exfalso
      apply h_ne
      have : q c = (r_target.val : ℤ) := by
        simp [r_target, h_toNat_eq]
      rw [this]
      push_cast
      have : (c.val : ℤ) / n = 0 := by
        apply Int.ediv_eq_zero_of_lt <;> [omega; exact Int.ofNat_lt.mpr c.isLt]
      have hn_ne : (n : ℤ) ≠ 0 := by omega
      rw [Int.add_comm, Int.mul_comm, Int.add_mul_ediv_left _ _ hn_ne, this]
      simp
    · intro j h_j_lt
      simp only [decide_eq_true_eq]
      unfold lift
      have h_c_mod : c.val % n = c.val := Nat.mod_eq_of_lt c.isLt
      have h_mod : (j.val * n + c.val) % n = c.val := by
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left]
        exact h_c_mod
      have h_div : (j.val * n + c.val) / n = j.val := by
        have hn_pos : 0 < n := hn
        rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hn_pos]
        have : c.val / n = 0 := Nat.div_eq_zero_iff.mpr (Or.inr c.isLt)
        omega
      simp only [h_mod, ite_eq_left_iff]
      intro h_eq_fn
      exfalso
      have : (j.val : ℤ) = r_target.val := by
        have h_eq : q c = ((j.val : ℤ) * n + c.val) / n := by
          by_contra h
          have : q ⟨c.val, c.isLt⟩ ≠ (((j.val * n + c.val) : ℕ) : ℤ) / n := h
          have h_contra : (0 : IntDomain) = 1 := h_eq_fn this
          norm_num at h_contra
        push_cast at h_eq
        have hn_ne : (n : ℤ) ≠ 0 := by omega
        have h_c_div : (c.val : ℤ) / n = 0 := by
          apply Int.ediv_eq_zero_of_lt <;> [omega; exact Int.ofNat_lt.mpr c.isLt]
        rw [Int.add_comm, Int.mul_comm, Int.add_mul_ediv_left _ _ hn_ne, h_c_div, zero_add] at h_eq
        have h_target : q c = (r_target.val : ℤ) := by
          simp [r_target, h_toNat_eq]
        rw [h_target] at h_eq
        exact h_eq.symm
      omega
  rw [h_find]
  simp
  rw [← h_toNat_eq]

/-- A 2D solution has exactly one queen per column -/
lemma col_has_exactly_one (x : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (nqueens_csp2D n) x) (c : Fin n) :
    ∃! r : Fin n, x (varIndex r c) = 1 := by
  have h_mem : sum_eq (col_variables c) 1 ∈ (nqueens_csp2D n).constraints := by
    unfold nqueens_csp2D
    simp [col_constraints2D, List.finRange]
  have h_sat₀ : IntCSP.satisfiesConstraintInt (sum_eq (col_variables c) 1) x :=
    h_sol (sum_eq (col_variables c) 1) h_mem
  have h_sat := (sum_eq_holds_iff _ _ _).mp h_sat₀
  unfold col_variables at h_sat
  simp only [_root_.Vector.toList_ofFn, List.map_ofFn] at h_sat
  have h_binary : ∀ r : Fin n, x (varIndex r c) = 0 ∨ x (varIndex r c) = 1 := by
    intro r
    have h_bound_mem : bound (varIndex r c) 0 1 ∈ (nqueens_csp2D n).constraints := by
      unfold nqueens_csp2D
      simp [bound_constraints2D, List.finRange]
    have h_bound_sat := (bound_holds_iff _ _ _ _).mp
      (h_sol (bound (varIndex r c) 0 1) h_bound_mem)
    have h_lb := h_bound_sat.1
    have h_ub := h_bound_sat.2
    by_cases h_eq_zero : x (varIndex r c) = 0
    · left; exact h_eq_zero
    · right
      have h_pos : 0 < x (varIndex r c) := by
        have : 0 ≠ x (varIndex r c) := by exact fun a => h_eq_zero (id (Eq.symm a))
        exact Std.lt_of_le_of_ne h_lb this
      have h_not_gt_one : ¬(1 < x (varIndex r c)) := by exact Int.not_lt_of_ge h_ub
      have : x (varIndex r c) = 1 := by exact Eq.symm (Int.le_antisymm h_pos h_ub)
      exact this
  have h_sum_varIndex : (List.ofFn fun r : Fin n => x (varIndex r c)).sum = 1 := h_sat

  have h_exists : ∃ r : Fin n, x (varIndex r c) = 1 := by
    by_contra h_none
    push Not at h_none
    have h_all_zero : ∀ r : Fin n, x (varIndex r c) = 0 := by
      intro r
      cases h_binary r with
      | inl h => exact h
      | inr h => exact absurd h (h_none r)
    have h_sum_zero : (List.ofFn fun r : Fin n => x (varIndex r c)).sum = 0 := by
      have : (fun r : Fin n => x (varIndex r c)) = (fun _ => 0) := by
        funext r
        exact h_all_zero r
      simp [this]
    rw [h_sum_zero] at h_sum_varIndex
    exact absurd h_sum_varIndex (by norm_num)

  have h_unique : ∀ r₁ r₂ : Fin n, x (varIndex r₁ c) = 1 → x (varIndex r₂ c) = 1 → r₁ = r₂ := by
    intro r₁ r₂ h₁ h₂
    by_contra h_ne
    have h_two : x (varIndex r₁ c) + x (varIndex r₂ c) = 2 := by
      rw [h₁, h₂]
      norm_num
    have h_nonneg : ∀ r : Fin n, 0 ≤ x (varIndex r c) := by
      intro r
      cases h_binary r with
      | inl h => rw [h];
      | inr h => rw [h]; norm_num
    have h_sum_ge_2 : (List.ofFn fun r : Fin n => x (varIndex r c)).sum ≥ 2 := by
      have h_eq_finset : (List.ofFn fun r : Fin n => x (varIndex r c)).sum =
                         (Finset.univ : Finset (Fin n)).sum (fun r => x (varIndex r c)) := by
        have : (List.ofFn fun r : Fin n => x (varIndex r c)) = List.map (fun r => x (varIndex r c)) (List.finRange n) := by
          rw [List.ofFn_eq_map]
        rw [this]
        rw [← List.sum_toFinset _ (List.nodup_finRange n)]
        congr 1
        exact List.toFinset_finRange n
      rw [h_eq_finset]
      have h_decomp : (Finset.univ : Finset (Fin n)).sum (fun r => x (varIndex r c)) =
                      x (varIndex r₁ c) + x (varIndex r₂ c) +
                      ((Finset.univ : Finset (Fin n)) \ {r₁, r₂}).sum (fun r => x (varIndex r c)) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ {r₁, r₂})]
        have h_pair_sum : ({r₁, r₂} : Finset (Fin n)).sum (fun r => x (varIndex r c)) =
                          x (varIndex r₁ c) + x (varIndex r₂ c) := by
          rw [Finset.sum_pair h_ne]
        rw [h_pair_sum, add_comm]
      rw [h_decomp]
      have h_rest_nonneg : 0 ≤ ((Finset.univ : Finset (Fin n)) \ {r₁, r₂}).sum (fun r => x (varIndex r c)) := by
        apply Finset.sum_nonneg
        intros r _
        exact h_nonneg r
      calc x (varIndex r₁ c) + x (varIndex r₂ c) +
           ((Finset.univ : Finset (Fin n)) \ {r₁, r₂}).sum (fun r => x (varIndex r c))
          ≥ x (varIndex r₁ c) + x (varIndex r₂ c) + 0 := by linarith
        _ = 1 + 1 + 0 := by rw [h₁, h₂]
        _ = 2 := by norm_num
    linarith

  cases h_exists with
  | intro r_wit h_wit =>
    use r_wit
    constructor
    · exact h_wit
    · intro r' h_r'
      exact (h_unique r_wit r' h_wit h_r').symm

/-- A 2D solution has exactly one queen per row -/
lemma row_has_exactly_one (x : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (nqueens_csp2D n) x) (r : Fin n) :
    ∃! c : Fin n, x (varIndex r c) = 1 := by
  have h_mem : sum_eq (row_variables r) 1 ∈ (nqueens_csp2D n).constraints := by
    unfold nqueens_csp2D
    simp [row_constraints2D, List.finRange]
  have h_sat₀ : IntCSP.satisfiesConstraintInt (sum_eq (row_variables r) 1) x :=
    h_sol (sum_eq (row_variables r) 1) h_mem
  have h_sat := (sum_eq_holds_iff _ _ _).mp h_sat₀
  unfold row_variables at h_sat
  simp only [_root_.Vector.toList_ofFn, List.map_ofFn] at h_sat
  have h_binary : ∀ c : Fin n, x (varIndex r c) = 0 ∨ x (varIndex r c) = 1 := by
    intro c
    have h_bound_mem : bound (varIndex r c) 0 1 ∈ (nqueens_csp2D n).constraints := by
      unfold nqueens_csp2D
      simp [bound_constraints2D, List.finRange]
    have h_bound_sat := (bound_holds_iff _ _ _ _).mp
      (h_sol (bound (varIndex r c) 0 1) h_bound_mem)
    have h_lb := h_bound_sat.1
    have h_ub := h_bound_sat.2
    by_cases h_eq_zero : x (varIndex r c) = 0
    · left; exact h_eq_zero
    · right
      have h_pos : 0 < x (varIndex r c) := by
        have : 0 ≠ x (varIndex r c) := by exact fun a => h_eq_zero (id (Eq.symm a))
        exact Std.lt_of_le_of_ne h_lb this
      have h_not_gt_one : ¬(1 < x (varIndex r c)) := by exact Int.not_lt_of_ge h_ub
      have : x (varIndex r c) = 1 := by exact Eq.symm (Int.le_antisymm h_pos h_ub)
      exact this
  have h_sum_varIndex : (List.ofFn fun c : Fin n => x (varIndex r c)).sum = 1 := h_sat

  have h_exists : ∃ c : Fin n, x (varIndex r c) = 1 := by
    by_contra h_none
    push Not at h_none
    have h_all_zero : ∀ c : Fin n, x (varIndex r c) = 0 := by
      intro c
      cases h_binary c with
      | inl h => exact h
      | inr h => exact absurd h (h_none c)
    have h_sum_zero : (List.ofFn fun c : Fin n => x (varIndex r c)).sum = 0 := by
      have : (fun c : Fin n => x (varIndex r c)) = (fun _ => 0) := by
        funext c
        exact h_all_zero c
      simp [this]
    rw [h_sum_zero] at h_sum_varIndex
    exact absurd h_sum_varIndex (by norm_num)

  have h_unique : ∀ c₁ c₂ : Fin n, x (varIndex r c₁) = 1 → x (varIndex r c₂) = 1 → c₁ = c₂ := by
    intro c₁ c₂ h₁ h₂
    by_contra h_ne
    have h_two : x (varIndex r c₁) + x (varIndex r c₂) = 2 := by
      rw [h₁, h₂]
      norm_num
    have h_nonneg : ∀ c : Fin n, 0 ≤ x (varIndex r c) := by
      intro c
      cases h_binary c with
      | inl h => rw [h];
      | inr h => rw [h]; norm_num
    have h_sum_ge_2 : (List.ofFn fun c : Fin n => x (varIndex r c)).sum ≥ 2 := by
      have h_eq_finset : (List.ofFn fun c : Fin n => x (varIndex r c)).sum =
                         (Finset.univ : Finset (Fin n)).sum (fun c => x (varIndex r c)) := by
        have : (List.ofFn fun c : Fin n => x (varIndex r c)) = List.map (fun c => x (varIndex r c)) (List.finRange n) := by
          rw [List.ofFn_eq_map]
        rw [this]
        rw [← List.sum_toFinset _ (List.nodup_finRange n)]
        congr 1
        exact List.toFinset_finRange n
      rw [h_eq_finset]
      have h_decomp : (Finset.univ : Finset (Fin n)).sum (fun c => x (varIndex r c)) =
                      x (varIndex r c₁) + x (varIndex r c₂) +
                      ((Finset.univ : Finset (Fin n)) \ {c₁, c₂}).sum (fun c => x (varIndex r c)) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ {c₁, c₂})]
        have h_pair_sum : ({c₁, c₂} : Finset (Fin n)).sum (fun c => x (varIndex r c)) =
                          x (varIndex r c₁) + x (varIndex r c₂) := by
          rw [Finset.sum_pair h_ne]
        rw [h_pair_sum, add_comm]
      rw [h_decomp]
      have h_rest_nonneg : 0 ≤ ((Finset.univ : Finset (Fin n)) \ {c₁, c₂}).sum (fun c => x (varIndex r c)) := by
        apply Finset.sum_nonneg
        intros c _
        exact h_nonneg c
      calc x (varIndex r c₁) + x (varIndex r c₂) +
           ((Finset.univ : Finset (Fin n)) \ {c₁, c₂}).sum (fun c => x (varIndex r c))
          ≥ x (varIndex r c₁) + x (varIndex r c₂) + 0 := by linarith
        _ = 1 + 1 + 0 := by rw [h₁, h₂]
        _ = 2 := by norm_num
    linarith

  cases h_exists with
  | intro c_wit h_wit =>
    use c_wit
    constructor
    · exact h_wit
    · intro c' h_c'
      exact (h_unique c_wit c' h_wit h_c').symm

/-- A 1D solution has bounds 0 ≤ q(c) < n -/
lemma solution_1D_bounds (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) (c : Fin n) :
    0 ≤ q c ∧ q c < n := by
  have h_mem : bound c 0 (n-1) ∈ (nqueens_csp1D n).constraints := by
    unfold nqueens_csp1D
    simp [bound_constraints1D, List.finRange]
  have h_sat := (bound_holds_iff _ _ _ _).mp (h_sol (bound c 0 (n-1)) h_mem)
  constructor
  · exact h_sat.1
  · exact lt_of_le_of_lt h_sat.2 (sub_one_lt _)

/-- A 1D solution is injective (from AllDifferent) -/
lemma solution_1D_injective (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) :
    Function.Injective q := by
  have h_mem : row_constraint1D n ∈ (nqueens_csp1D n).constraints := by
    unfold nqueens_csp1D
    simp [row_constraint1D]
  have h_nodup : (List.ofFn q).Nodup :=
    (alldifferent_all_holds_iff _).mp (h_sol (row_constraint1D n) h_mem)
  rw [List.nodup_iff_injective_get] at h_nodup
  have h_sat := h_nodup
  intro i j h_eq
  have h_get_eq : (List.ofFn q).get ⟨i.val, by simp⟩ =
                  (List.ofFn q).get ⟨j.val, by simp⟩ := by
    simp
    exact h_eq
  have h_indices := h_sat h_get_eq
  simp at h_indices
  exact Fin.ext h_indices

/-- Division of varIndex gives the row -/
lemma varIndex_div_eq (r c : Fin n) (hn : 0 < n) : (varIndex r c).val / n = r.val := by
  unfold varIndex
  simp only
  have : c.val < n := c.isLt
  have : (r.val * n + c.val) / n = r.val + c.val / n := by
    rw [Nat.add_comm, Nat.mul_comm]
    rw [Nat.add_mul_div_left _ _ hn]
    rw [Nat.add_comm]
  rw [this]
  have : c.val / n = 0 := Nat.div_eq_zero_iff.mpr (Or.inr c.isLt)
  omega

/-- Modulo of varIndex gives the column -/
lemma varIndex_mod_eq (r c : Fin n) : (varIndex r c).val % n = c.val := by
  simp [varIndex, Nat.mul_add_mod_of_lt c.isLt]

/-- varIndex is in the antidiagonal with sum r + c -/
lemma varIndex_in_antidiag (r c : Fin n) (hn : 0 < n) :
    varIndex r c ∈ antidiag_variables ((r.val : ℤ) + c.val) := by
  unfold antidiag_variables varIndex
  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
  constructor
  · trivial
  · push_cast
    have hn_ne : (n : ℤ) ≠ 0 := by omega
    rw [Int.add_comm (↑r.val * ↑n), Int.mul_comm ↑r.val ↑n]
    rw [Int.add_mul_ediv_left _ _ hn_ne]
    have h_c_lt : 0 ≤ (c.val : ℤ) ∧ (c.val : ℤ) < (n : ℤ) := by omega
    have h_div_zero : (c.val : ℤ) / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt h_c_lt.1 h_c_lt.2
    rw [h_div_zero, Int.zero_add]
    rw [Int.add_mul_emod_self_left]
    have h_mod : (c.val : ℤ) % (n : ℤ) = c.val := Int.emod_eq_of_lt h_c_lt.1 h_c_lt.2
    rw [h_mod]

/-- varIndex is in the diagonal with difference r - c -/
lemma varIndex_in_diag (r c : Fin n) (hn : 0 < n) :
    varIndex r c ∈ diag_variables ((r.val : ℤ) - c.val) := by
  unfold diag_variables varIndex
  simp only [List.mem_filter, List.mem_finRange, decide_eq_true_eq]
  constructor
  · trivial
  · push_cast
    have hn_ne : (n : ℤ) ≠ 0 := by omega
    rw [Int.add_comm (↑r.val * ↑n), Int.mul_comm ↑r.val ↑n]
    rw [Int.add_mul_ediv_left _ _ hn_ne]
    have h_c_lt : 0 ≤ (c.val : ℤ) ∧ (c.val : ℤ) < (n : ℤ) := by omega
    have h_div_zero : (c.val : ℤ) / (n : ℤ) = 0 := Int.ediv_eq_zero_of_lt h_c_lt.1 h_c_lt.2
    rw [h_div_zero, Int.zero_add]
    rw [Int.add_mul_emod_self_left]
    have h_mod : (c.val : ℤ) % (n : ℤ) = c.val := Int.emod_eq_of_lt h_c_lt.1 h_c_lt.2
    rw [h_mod]

/-- varIndex is injective in both arguments -/
lemma varIndex_injective (hn : 0 < n) : ∀ r₁ c₁ r₂ c₂ : Fin n,
    varIndex r₁ c₁ = varIndex r₂ c₂ → r₁ = r₂ ∧ c₁ = c₂ := by
  intro r₁ c₁ r₂ c₂ h_eq
  have h_div₁ := varIndex_div_eq r₁ c₁
  have h_div₂ := varIndex_div_eq r₂ c₂
  have h_mod₁ := varIndex_mod_eq r₁ c₁
  have h_mod₂ := varIndex_mod_eq r₂ c₂
  rw [h_eq] at h_div₁ h_mod₁
  have h_r : r₁.val = r₂.val := by
    have : r₁.val = (varIndex r₂ c₂).val / n := by
      exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (congrArg Nat.succ (h_div₁ hn)))
    rw [h_div₂] at this
    exact this
    exact hn
  have h_c : c₁.val = c₂.val := by
    have : c₁.val = (varIndex r₂ c₂).val % n := h_mod₁.symm
    rw [h_mod₂] at this
    exact this
  exact ⟨Fin.ext h_r, Fin.ext h_c⟩

/-- π equals the row where the queen is located -/
lemma π_eq_row_of_queen (x : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (nqueens_csp2D n) x)
    (c : Fin n) (r : Fin n) (h : x (varIndex r c) = 1) :
    π x c = r.val := by
  have h_unique := col_has_exactly_one x h_sol c
  obtain ⟨r_unique, h_val, h_unique_prop⟩ := h_unique
  have h_r_eq : r = r_unique := h_unique_prop r h
  subst h_r_eq
  unfold π
  classical
  cases h_find : (List.finRange n).find? (fun r' => decide (x (varIndex r' c) = 1)) with
  | none =>
      exfalso
      have : ((List.finRange n).find? (fun r' => decide (x (varIndex r' c) = 1))).isSome := by
        have : ∃ b ∈ List.finRange n, decide (x (varIndex b c) = 1) = true := by
          use r
          constructor
          · simp [List.mem_finRange]
          · exact decide_eq_true_eq.mpr h
        exact List.find?_isSome.2 this
      simp [h_find] at this
  | some r' =>
      have hr'_sat : decide (x (varIndex r' c) = 1) = true := by
        have : (fun r' => decide (x (varIndex r' c) = 1)) r' = true :=
          @List.find?_some _ (fun r' => decide (x (varIndex r' c) = 1)) r' (List.finRange n) h_find
        exact this
      have hr'_val : x (varIndex r' c) = 1 := decide_eq_true_eq.mp hr'_sat
      have hr'_eq : r' = r := h_unique_prop r' hr'_val
      have h_list_eq : (List.finRange n).find? (fun r_tmp => decide (x ⟨r_tmp.val * n + c.val,
        by
          have h1 : r_tmp.val < n := r_tmp.isLt
          have h2 : c.val < n := c.isLt
          calc r_tmp.val * n + c.val
              < r_tmp.val * n + n := Nat.add_lt_add_left h2 _
            _ = (r_tmp.val + 1) * n := by ring
            _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩
        = 1)) = (List.finRange n).find? (fun r_tmp => decide (x (varIndex r_tmp c) = 1)) := by
        congr 1
      rw [h_list_eq, h_find]
      simp [hr'_eq]

end AuxiliaryLemmas

-- ============================================================================
-- Forward Direction: 2D → 1D
-- ============================================================================

section ForwardDirection

variable {n : ℕ} (hn : 0 < n)

/-- π preserves bounds -/
lemma π_preserves_bounds (x : IntAssignment (n*n))
   (c : Fin n) :
    0 ≤ π x c ∧ π x c < n := by
  unfold π
  cases h : (List.finRange n).find? (fun r => x ⟨r.val * n + c.val, by
    have h1 : r.val < n := r.isLt
    have h2 : c.val < n := c.isLt
    calc r.val * n + c.val
        < r.val * n + n := Nat.add_lt_add_left h2 _
      _ = (r.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩ = 1)
  case none =>
    simp
    exact Fin.pos c
  case some r =>
    simp

/-- Helper: find? returns some when there's a unique element satisfying the predicate -/
lemma find?_eq_some_of_exists_unique {α : Type*} {l : List α} {p : α → Bool} {a : α}
    (ha : a ∈ l) (hp : p a = true)
    (huniq : ∀ b, b ∈ l → p b = true → b = a) :
    l.find? p = some a := by
  classical
  cases h : l.find? p with
  | none =>
      exfalso
      have : (l.find? p).isSome := by
        have : ∃ b ∈ l, p b = true := ⟨a, ha, hp⟩
        exact List.find?_isSome.2 this
      simp [h] at this
  | some b =>
      have hb : p b = true := List.find?_some h
      have hbeq : b = a := huniq b (List.mem_of_find?_eq_some h) hb
      simp [hbeq]

/-- π preserves AllDifferent (injectivity) -/
lemma π_preserves_alldifferent (x : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (nqueens_csp2D n) x) :
    Function.Injective (π x) := by
  intro c₁ c₂ h_eq
  by_contra h_ne

  have h_c₁ := col_has_exactly_one x h_sol c₁
  have h_c₂ := col_has_exactly_one x h_sol c₂
  obtain ⟨r₁, h_r₁_val, h_r₁_unique⟩ := h_c₁
  obtain ⟨r₂, h_r₂_val, h_r₂_unique⟩ := h_c₂

  have hfind₁ : (List.finRange n).find? (fun r => decide (x (varIndex r c₁) = 1)) = some r₁ := by
    have hr₁_mem : r₁ ∈ List.finRange n := by simp [List.mem_finRange]
    apply find?_eq_some_of_exists_unique hr₁_mem
    · exact decide_eq_true_eq.mpr h_r₁_val
    · intro r' hmem hpr'
      have hr'_val : x (varIndex r' c₁) = 1 := decide_eq_true_eq.mp hpr'
      exact h_r₁_unique r' hr'_val

  have hfind₂ : (List.finRange n).find? (fun r => decide (x (varIndex r c₂) = 1)) = some r₂ := by
    have hr₂_mem : r₂ ∈ List.finRange n := by simp [List.mem_finRange]
    apply find?_eq_some_of_exists_unique hr₂_mem
    · exact decide_eq_true_eq.mpr h_r₂_val
    · intro r' hmem hpr'
      have hr'_val : x (varIndex r' c₂) = 1 := decide_eq_true_eq.mp hpr'
      exact h_r₂_unique r' hr'_val

  have hπ₁ : π x c₁ = (r₁.val : ℤ) := by
    unfold π
    have : (fun r => decide (x ⟨r.val * n + c₁.val, by
      calc r.val * n + c₁.val
        < r.val * n + n := Nat.add_lt_add_left c₁.isLt (r.val * n)
        _ = (r.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr r.isLt)
    ⟩ = 1)) =
           (fun r => decide (x (varIndex r c₁) = 1)) := by
      funext r; rfl
    simp only [this, hfind₁]

  have hπ₂ : π x c₂ = (r₂.val : ℤ) := by
    unfold π
    have : (fun r => decide (x ⟨r.val * n + c₂.val, by
      calc r.val * n + c₂.val
        < r.val * n + n := Nat.add_lt_add_left c₂.isLt (r.val * n)
        _ = (r.val + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr r.isLt)
    ⟩ = 1)) =
           (fun r => decide (x (varIndex r c₂) = 1)) := by
      funext r; rfl
    simp only [this, hfind₂]

  have h_r_eq : r₁ = r₂ := by
    have : (r₁.val : ℤ) = (r₂.val : ℤ) := by rw [← hπ₁, ← hπ₂, h_eq]
    exact Fin.ext (Int.ofNat_inj.mp this)

  rw [h_r_eq] at h_r₁_val

  have h_row := row_has_exactly_one x h_sol r₂
  obtain ⟨c_wit, h_wit, h_c_unique⟩ := h_row

  have h_c₁_eq : c₁ = c_wit := h_c_unique c₁ h_r₁_val
  have h_c₂_eq : c₂ = c_wit := h_c_unique c₂ h_r₂_val

  have : c₁ = c₂ := by rw [h_c₁_eq, h_c₂_eq]
  exact h_ne this

/-- π preserves positive diagonal constraint -/
lemma π_preserves_diag_pos (hn : 0 < n) (x : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (nqueens_csp2D n) x) :
    List.Nodup (List.ofFn fun i : Fin n => π x i + (i.val : ℤ)) := by
  rw [List.nodup_ofFn]
  intro i j h_eq

  have h_col_i := col_has_exactly_one x h_sol i
  have h_col_j := col_has_exactly_one x h_sol j
  obtain ⟨r_i, h_r_i_val, h_r_i_unique⟩ := h_col_i
  obtain ⟨r_j, h_r_j_val, h_r_j_unique⟩ := h_col_j

  have hπ_i : π x i = r_i.val := π_eq_row_of_queen x h_sol i r_i h_r_i_val
  have hπ_j : π x j = r_j.val := π_eq_row_of_queen x h_sol j r_j h_r_j_val

  have h_eq_simple : π x i + (i.val : ℤ) = π x j + (j.val : ℤ) := h_eq
  rw [hπ_i, hπ_j] at h_eq_simple

  have h_same_antidiag : (r_i.val : ℤ) + (i.val : ℤ) = (r_j.val : ℤ) + (j.val : ℤ) := h_eq_simple

  have h_var_i_in : varIndex r_i i ∈ antidiag_variables ((r_i.val : ℤ) + (i.val : ℤ)) :=
    varIndex_in_antidiag r_i i hn
  have h_var_j_in : varIndex r_j j ∈ antidiag_variables ((r_j.val : ℤ) + (j.val : ℤ)) :=
    varIndex_in_antidiag r_j j hn

  rw [h_same_antidiag] at h_var_i_in

  by_contra h_ne

  have h_var_ne : varIndex r_i i ≠ varIndex r_j j := by
    intro h_var_eq
    have ⟨_, h_c_eq⟩ := varIndex_injective hn r_i i r_j j h_var_eq
    exact h_ne h_c_eq

  have h_val_i : x (varIndex r_i i) = 1 := h_r_i_val
  have h_val_j : x (varIndex r_j j) = 1 := h_r_j_val

  let k := r_i.val + i.val

  have h_k_range : k < 2*n - 1 := by
    unfold k
    have : r_i.val < n := r_i.isLt
    have : i.val < n := i.isLt
    omega

  have h_nonempty : @antidiag_variables n (k : ℤ) ≠ [] := by
    intro h_empty
    have h_in_empty : varIndex r_i i ∈ @antidiag_variables n (k : ℤ) := by
      unfold k
      convert h_var_i_in using 2
    rw [h_empty] at h_in_empty
    have h_not_in_empty : varIndex r_i i ∉ [] := by exact List.not_mem_nil
    contradiction


  have h_constraint_mem : sum_le (listToVector (@antidiag_variables n (k : ℤ))) 1 ∈
      (nqueens_csp2D n).constraints := by
    unfold nqueens_csp2D
    simp only [List.mem_append]
    right
    unfold antidiag_constraints2D
    simp [List.mem_filterMap]
    use k
    constructor
    · exact h_k_range
    · simp

  have h_sat₀ : IntCSP.satisfiesConstraintInt
      (sum_le (listToVector (@antidiag_variables n (k : ℤ))) 1) x :=
    h_sol (sum_le (listToVector (@antidiag_variables n (k : ℤ))) 1) h_constraint_mem
  have h_sat := (sum_le_holds_iff _ _ _).mp h_sat₀

  have h_i_in_k : varIndex r_i i ∈ @antidiag_variables n (k : ℤ) := by
    unfold k
    convert h_var_i_in using 2
  have h_j_in_k : varIndex r_j j ∈ @antidiag_variables n (k : ℤ) := by
    unfold k
    simp [h_same_antidiag]
    exact h_var_j_in

  have h_bounds : ∀ v ∈ @antidiag_variables n (k : ℤ), 0 ≤ x v ∧ x v ≤ 1 := by
    intro v h_v_in
    have h_bound_mem : bound v 0 1 ∈ (nqueens_csp2D n).constraints := by
      unfold nqueens_csp2D
      simp [bound_constraints2D, List.finRange]
    exact (bound_holds_iff _ _ _ _).mp (h_sol (bound v 0 1) h_bound_mem)

  have h_sum_ge_2 : ((@antidiag_variables n (k : ℤ)).map x).sum ≥ 2 := by
    have h_i_in_map : 1 ∈ (@antidiag_variables n (k : ℤ)).map x := by
      simp [List.mem_map]
      use varIndex r_i i
    have h_j_in_map : 1 ∈ (@antidiag_variables n (k : ℤ)).map x := by
      simp [List.mem_map]
      use varIndex r_j j

    have h_all_nonneg : ∀ y ∈ (@antidiag_variables n (k : ℤ)).map x, 0 ≤ y := by
      intro y hy
      simp [List.mem_map] at hy
      obtain ⟨v, hv_in, hv_eq⟩ := hy
      rw [← hv_eq]
      exact (h_bounds v hv_in).1

    calc ((@antidiag_variables n (k : ℤ)).map x).sum
        ≥ x (varIndex r_i i) + x (varIndex r_j j) := by
          have h_nodup_antidiag : (@antidiag_variables n (k : ℤ)).Nodup := by
            -- antidiag_variables is a filter on finRange, which has no duplicates
            unfold antidiag_variables
            exact List.Nodup.filter _ (List.nodup_finRange _)

          have h_eq_finset : ((@antidiag_variables n (k : ℤ)).map x).sum =
                             (@antidiag_variables n (k : ℤ)).toFinset.sum (fun v => x v) := by
            rw [← List.sum_toFinset _ h_nodup_antidiag]

          rw [h_eq_finset]
          have h_decomp : (@antidiag_variables n (k : ℤ)).toFinset.sum (fun v => x v) =
                          x (varIndex r_i i) + x (varIndex r_j j) +
                          ((@antidiag_variables n (k : ℤ)).toFinset \ {varIndex r_i i, varIndex r_j j}).sum (fun v => x v) := by
            have h_both_in : {varIndex r_i i, varIndex r_j j} ⊆ (@antidiag_variables n (k : ℤ)).toFinset := by
              intro v hv
              rw [Finset.mem_insert, Finset.mem_singleton] at hv
              rw [List.mem_toFinset]
              cases hv with
              | inl h => rw [h]; exact h_i_in_k
              | inr h => rw [h]; exact h_j_in_k
            rw [← Finset.sum_sdiff h_both_in]
            have h_pair_sum : ({varIndex r_i i, varIndex r_j j} : Finset _).sum (fun v => x v) =
                              x (varIndex r_i i) + x (varIndex r_j j) := by
              rw [Finset.sum_pair h_var_ne]
            rw [h_pair_sum, add_comm]

          rw [h_decomp]
          have h_rest_nonneg : 0 ≤ ((@antidiag_variables n (k : ℤ)).toFinset \ {varIndex r_i i, varIndex r_j j}).sum (fun v => x v) := by
            apply Finset.sum_nonneg
            intros v hv
            have hv_in : v ∈ @antidiag_variables n (k : ℤ) := by
              have : v ∈ (@antidiag_variables n (k : ℤ)).toFinset := Finset.sdiff_subset hv
              rw [List.mem_toFinset] at this
              exact this
            exact (h_bounds v hv_in).1

          -- So the sum is at least x(varIndex r_i i) + x(varIndex r_j j)
          linarith
      _ = 1 + 1 := by rw [h_val_i, h_val_j]
      _ = 2 := by norm_num

  have h_sat_converted : ((@antidiag_variables n (k : ℤ)).map x).sum ≤ 1 := h_sat

  -- Now we have a contradiction: sum ≥ 2 but sum ≤ 1
  linarith

/-- π preserves negative diagonal constraint -/
lemma π_preserves_diag_neg (hn : 0 < n) (x : IntAssignment (n*n))
    (h_sol : IntCSP.isSolutionInt (nqueens_csp2D n) x) :
    List.Nodup (List.ofFn fun i : Fin n => π x i - (i.val : ℤ)) := by
  rw [List.nodup_ofFn]
  intro i j h_eq

  have h_col_i := col_has_exactly_one x h_sol i
  have h_col_j := col_has_exactly_one x h_sol j
  obtain ⟨r_i, h_r_i_val, h_r_i_unique⟩ := h_col_i
  obtain ⟨r_j, h_r_j_val, h_r_j_unique⟩ := h_col_j

  have hπ_i : π x i = r_i.val := π_eq_row_of_queen x h_sol i r_i h_r_i_val
  have hπ_j : π x j = r_j.val := π_eq_row_of_queen x h_sol j r_j h_r_j_val

  have h_eq_simple : π x i - (i.val : ℤ) = π x j - (j.val : ℤ) := h_eq
  rw [hπ_i, hπ_j] at h_eq_simple

  have h_same_diag : (r_i.val : ℤ) - (i.val : ℤ) = (r_j.val : ℤ) - (j.val : ℤ) := h_eq_simple

  have h_var_i_in : varIndex r_i i ∈ diag_variables ((r_i.val : ℤ) - (i.val : ℤ)) :=
    varIndex_in_diag r_i i hn
  have h_var_j_in : varIndex r_j j ∈ diag_variables ((r_j.val : ℤ) - (j.val : ℤ)) :=
    varIndex_in_diag r_j j hn

  rw [h_same_diag] at h_var_i_in

  by_contra h_ne

  have h_var_ne : varIndex r_i i ≠ varIndex r_j j := by
    intro h_var_eq
    have ⟨_, h_c_eq⟩ := varIndex_injective hn r_i i r_j j h_var_eq
    exact h_ne h_c_eq

  have h_val_i : x (varIndex r_i i) = 1 := h_r_i_val
  have h_val_j : x (varIndex r_j j) = 1 := h_r_j_val

  let d := (r_i.val : ℤ) - (i.val : ℤ)

  let k_nat := r_i.val + (n - 1) - i.val

  have h_k_range : k_nat < 2*n - 1 := by
    unfold k_nat
    have : r_i.val < n := r_i.isLt
    have : i.val < n := i.isLt
    omega

  have h_k_eq_d : (k_nat : ℤ) - ((n : ℤ) - 1) = d := by
    unfold k_nat d
    have : r_i.val < n := r_i.isLt
    have : i.val < n := i.isLt
    omega

  have h_nonempty : @diag_variables n d ≠ [] := by
    intro h_empty
    have h_in_empty : varIndex r_i i ∈ @diag_variables n d := by
      unfold d
      convert h_var_i_in using 2
    rw [h_empty] at h_in_empty
    have h_not_in_empty : varIndex r_i i ∉ [] := by exact List.not_mem_nil
    contradiction

  have h_constraint_mem : sum_le (listToVector (@diag_variables n d)) 1 ∈
      (nqueens_csp2D n).constraints := by
    unfold nqueens_csp2D
    simp only [List.mem_append]
    left
    right
    unfold diag_constraints2D
    simp [List.mem_filterMap]
    use k_nat
    constructor
    · exact h_k_range
    · rw [h_k_eq_d]
      split
      · contradiction
      · rfl

  have h_sat₀ : IntCSP.satisfiesConstraintInt
      (sum_le (listToVector (@diag_variables n d)) 1) x :=
    h_sol (sum_le (listToVector (@diag_variables n d)) 1) h_constraint_mem
  have h_sat := (sum_le_holds_iff _ _ _).mp h_sat₀

  have h_i_in_d : varIndex r_i i ∈ @diag_variables n d := by
    unfold d
    convert h_var_i_in using 2
  have h_j_in_d : varIndex r_j j ∈ @diag_variables n d := by
    unfold d
    simp [h_same_diag]
    exact h_var_j_in

  have h_bounds : ∀ v ∈ @diag_variables n d, 0 ≤ x v ∧ x v ≤ 1 := by
    intro v h_v_in
    have h_bound_mem : bound v 0 1 ∈ (nqueens_csp2D n).constraints := by
      unfold nqueens_csp2D
      simp [bound_constraints2D, List.finRange]
    exact (bound_holds_iff _ _ _ _).mp (h_sol (bound v 0 1) h_bound_mem)

  have h_sum_ge_2 : ((@diag_variables n d).map x).sum ≥ 2 := by
    have h_nodup_diag : (@diag_variables n d).Nodup := by
      unfold diag_variables
      exact List.Nodup.filter _ (List.nodup_finRange _)

    have h_eq_finset : ((@diag_variables n d).map x).sum =
                       (@diag_variables n d).toFinset.sum (fun v => x v) := by
      rw [← List.sum_toFinset _ h_nodup_diag]

    rw [h_eq_finset]
    have h_decomp : (@diag_variables n d).toFinset.sum (fun v => x v) =
                    x (varIndex r_i i) + x (varIndex r_j j) +
                    ((@diag_variables n d).toFinset \ {varIndex r_i i, varIndex r_j j}).sum (fun v => x v) := by
      have h_both_in : {varIndex r_i i, varIndex r_j j} ⊆ (@diag_variables n d).toFinset := by
        intro v hv
        rw [Finset.mem_insert, Finset.mem_singleton] at hv
        rw [List.mem_toFinset]
        cases hv with
        | inl h => rw [h]; exact h_i_in_d
        | inr h => rw [h]; exact h_j_in_d
      rw [← Finset.sum_sdiff h_both_in]
      have h_pair_sum : ({varIndex r_i i, varIndex r_j j} : Finset _).sum (fun v => x v) =
                        x (varIndex r_i i) + x (varIndex r_j j) := by
        rw [Finset.sum_pair h_var_ne]
      rw [h_pair_sum, add_comm]

    rw [h_decomp]
    have h_rest_nonneg : 0 ≤ ((@diag_variables n d).toFinset \ {varIndex r_i i, varIndex r_j j}).sum (fun v => x v) := by
      apply Finset.sum_nonneg
      intros v hv
      have hv_in : v ∈ @diag_variables n d := by
        have : v ∈ (@diag_variables n d).toFinset := Finset.sdiff_subset hv
        rw [List.mem_toFinset] at this
        exact this
      exact (h_bounds v hv_in).1

    linarith

  have h_sat_converted : ((@diag_variables n d).map x).sum ≤ 1 := h_sat

  -- Now we have a contradiction: sum ≥ 2 but sum ≤ 1
  linarith

/-- Forward direction: 2D solution projects to 1D solution -/
theorem forward_direction (hn : 0 < n) (sol₂ : IntAssignment (n*n))
    (h : IntCSP.isSolutionInt (nqueens_csp2D n) sol₂) :
    IntCSP.isSolutionInt (nqueens_csp1D n) (π sol₂) := by
  intro c h_c_in
  have h_c_in' : c ∈ bound_constraints1D n ∨ c = row_constraint1D n ∨
      c = diagonal_constraint1D n ∨ c = antidiagonal_constraint1D n := by
    have : c ∈ bound_constraints1D n ++ [row_constraint1D n] ++
        [diagonal_constraint1D n] ++ [antidiagonal_constraint1D n] := h_c_in
    rcases List.mem_append.mp this with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_singleton.mp h))
      · exact Or.inr (Or.inr (Or.inl (List.mem_singleton.mp h)))
    · exact Or.inr (Or.inr (Or.inr (List.mem_singleton.mp h)))
  rcases h_c_in' with h_bound | h_row | h_diag_neg | h_diag_pos
  · rw [bound_constraints1D] at h_bound
    obtain ⟨v, h_v_in, rfl⟩ := List.mem_map.mp h_bound
    show IntCSP.satisfiesConstraintInt (bound v 0 ((n : ℤ) - 1)) (π sol₂)
    rw [bound_holds_iff]
    obtain ⟨h_lb, h_ub⟩ := π_preserves_bounds sol₂ v
    exact ⟨h_lb, Int.le_sub_one_of_lt h_ub⟩
  · subst h_row
    show IntCSP.satisfiesConstraintInt (alldifferent_all n) (π sol₂)
    rw [alldifferent_all_holds_iff, List.nodup_ofFn]
    exact π_preserves_alldifferent sol₂ h
  · subst h_diag_neg
    show IntCSP.satisfiesConstraintInt (alldifferent_diag_neg n) (π sol₂)
    rw [diag_neg_holds_iff]
    exact π_preserves_diag_neg hn sol₂ h
  · subst h_diag_pos
    show IntCSP.satisfiesConstraintInt (alldifferent_diag_pos n) (π sol₂)
    rw [diag_pos_holds_iff]
    exact π_preserves_diag_pos hn sol₂ h

end ForwardDirection

-- ============================================================================
-- Backward Direction: 1D → 2D
-- ============================================================================

section BackwardDirection

variable {n : ℕ} (hn : 0 < n)

/-- lift produces binary values -/
lemma lift_binary (q : IntAssignment n) (v : Fin (n*n)) :
    lift hn q v = 0 ∨ lift hn q v = 1 := by
  simp [lift]; by_cases h : q ⟨v.val % n, Nat.mod_lt v.val hn⟩ = v.val / n <;> simp [h]

/-- Simplification of lift at varIndex -/
lemma lift_at_varIndex (q : IntAssignment n) (r c : Fin n) :
    lift hn q (varIndex r c) = if q c = (r.val : ℤ) then 1 else 0 := by
  unfold lift varIndex
  simp only
  have h_mod : (r.val * n + c.val) % n = c.val := by
    rw [Nat.add_comm, Nat.mul_comm]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt c.isLt
  have h_div : ((r.val * n + c.val) : ℤ) / (n : ℤ) = r.val := by
    have hn_ne : (n : ℤ) ≠ 0 := by omega
    rw [Int.add_comm, Int.mul_comm]
    rw [Int.add_mul_ediv_left _ _ hn_ne]
    have : (c.val : ℤ) / (n : ℤ) = 0 := by
      apply Int.ediv_eq_zero_of_lt <;> omega
    simp [this]
  have h_fin : ⟨(r.val * n + c.val) % n, Nat.mod_lt (r.val * n + c.val) hn⟩ = c := by
    ext
    exact h_mod
  rw [h_fin]
  by_cases h : q c = (r.val : ℤ)
  · simp only [h, ite_true, ite_eq_left_iff]
    exact fun a => False.elim (a (id (Eq.symm h_div)))
  · simp only [h, ite_false, ite_eq_right_iff]
    intro h_eq
    push_cast at h_eq
    rw [h_div] at h_eq
    exact False.elim (h h_eq)

lemma Fin_is_Finite : Finite (Fin n) := inferInstance

/-- A 1D solution is surjective (from injectivity on finite domain) -/
lemma solution_1D_surjective (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) :
    ∀ r : Fin n, ∃ c : Fin n, q c = (r.val : ℤ) := by
  intro r
  have h_inj := solution_1D_injective q h_sol
  have h_bounds := fun c => solution_1D_bounds q h_sol c
  let q' : Fin n → Fin n := fun c => ⟨(q c).toNat, by
    have h := h_bounds c
    have h_nonneg : 0 ≤ q c := h.1
    have h_lt : q c < n := h.2
    rw [Int.toNat_lt h_nonneg]
    omega⟩
  have h_inj' : Function.Injective q' := by
    intro c₁ c₂ h_eq
    simp only [q'] at h_eq
    have h₁ := h_bounds c₁
    have h₂ := h_bounds c₂
    have : Int.toNat (q c₁) = Int.toNat (q c₂) := Fin.ext_iff.mp h_eq
    have : q c₁ = q c₂ := by
      rw [← Int.toNat_of_nonneg h₁.1, ← Int.toNat_of_nonneg h₂.1, this]
    exact h_inj this
  have h_surj' : Function.Surjective q' := by
    haveI : Finite (Fin n) := by exact Fin_is_Finite
    exact Finite.injective_iff_surjective.mp h_inj'
  obtain ⟨c, hc⟩ := h_surj' r
  use c
  have h := h_bounds c
  simp only [q'] at hc
  have : Int.toNat (q c) = r.val := Fin.ext_iff.mp hc
  rw [← Int.toNat_of_nonneg h.1]
  simp only [this]


/-- A 1D solution gives unique column for each row (bijectivity) -/
lemma solution_1D_bijective (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) :
    ∀ r : Fin n, ∃! c : Fin n, q c = (r.val : ℤ) := by
  intro r
  obtain ⟨c₀, hc₀⟩ := solution_1D_surjective q h_sol r
  use c₀, hc₀
  intro c' hc'
  have h_inj := solution_1D_injective q h_sol
  have : q c₀ = q c' := by rw [hc₀, hc']
  exact h_inj this.symm

/-- A 1D solution gives unique row for each column value -/
lemma unique_row_for_column (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) (c : Fin n) :
    ∃! r : Fin n, q c = (r.val : ℤ) := by
  have h_bounds := solution_1D_bounds q h_sol c
  let r₀ : Fin n := ⟨(q c).toNat, by
    have h_nonneg : 0 ≤ q c := h_bounds.1
    have h_lt : q c < n := h_bounds.2
    rw [Int.toNat_lt h_nonneg]
    omega⟩
  use r₀
  constructor
  · show q c = (r₀.val : ℤ)
    simp only [r₀]
    exact (Int.toNat_of_nonneg h_bounds.1).symm
  · intro r' hr'
    ext
    simp only [r₀]
    have : (r'.val : ℤ) = q c := hr'.symm
    rw [← Int.toNat_of_nonneg h_bounds.1] at this
    exact Nat.cast_injective this

/-- Sum of indicator function with unique element equals 1 -/
lemma sum_indicator_unique {n : ℕ} (r : Fin n) (q : Fin n → ℤ)
    (h_unique : ∃! c₀ : Fin n, q c₀ = (r.val : ℤ)) :
    (List.ofFn fun c => if q c = (r.val : ℤ) then (1 : ℤ) else 0).sum = 1 := by
  obtain ⟨c₀, hc₀, h_uniq⟩ := h_unique
  have h_eq : (List.ofFn fun c => if q c = (r.val : ℤ) then (1 : ℤ) else 0).sum =
              ∑ c : Fin n, if q c = (r.val : ℤ) then (1 : ℤ) else 0 := by
    rw [List.ofFn_eq_map]
    exact rfl
  rw [h_eq]
  rw [Finset.sum_eq_single c₀]
  · simp [hc₀]
  · intro c _ hc_ne
    simp only [ite_eq_right_iff]
    intro hc
    exfalso
    have : c = c₀ := h_uniq c hc
    exact hc_ne this
  · intro h_not_mem
    exfalso
    exact h_not_mem (Finset.mem_univ c₀)

/-- Sum of index indicator function with unique index equals 1 -/
lemma sum_indicator_index_eq {n : ℕ} (val : ℤ)
    (h_unique : ∃! r₀ : Fin n, val = (r₀.val : ℤ)) :
    (List.ofFn (fun r : Fin n => if val = (r.val : ℤ) then (1 : ℤ) else 0)).sum = 1 := by
  obtain ⟨r₀, hr₀, h_uniq⟩ := h_unique
  have h_eq : (List.ofFn (fun r : Fin n => if val = (r.val : ℤ) then (1 : ℤ) else 0)).sum =
              ∑ r : Fin n, if val = (r.val : ℤ) then (1 : ℤ) else 0 := by
    rw [List.ofFn_eq_map]
    exact rfl
  rw [h_eq]
  rw [Finset.sum_eq_single r₀]
  · simp [hr₀]
  · intro r _ hr_ne
    simp only [ite_eq_right_iff]
    intro hr
    exfalso
    have : r = r₀ := h_uniq r hr
    exact hr_ne this
  · intro h_not_mem
    exfalso
    exact h_not_mem (Finset.mem_univ r₀)

/-- lift satisfies row constraints -/
lemma lift_satisfies_row_constraints (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) (r : Fin n) :
    (List.ofFn fun c : Fin n => lift hn q (varIndex r c)).sum = 1 := by
  -- Step 1: Rewrite using lift_at_varIndex
  have h_eq : (List.ofFn fun c : Fin n => lift hn q (varIndex r c)) =
              (List.ofFn fun c : Fin n => if q c = (r.val : ℤ) then 1 else 0) := by
    apply List.ext_get
    · simp
    · intro i h1 h2
      simp
      exact lift_at_varIndex hn q r ⟨i, by simp at h1; exact h1⟩
  rw [h_eq]
  -- Step 2: Apply sum_indicator_unique
  have h_unique := solution_1D_bijective q h_sol r
  exact sum_indicator_unique r q h_unique

/-- lift satisfies column constraints -/
lemma lift_satisfies_col_constraints (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) (c : Fin n) :
    (List.ofFn fun r : Fin n => lift hn q (varIndex r c)).sum = 1 := by
  -- Step 1: Rewrite using lift_at_varIndex
  have h_eq : (List.ofFn fun r : Fin n => lift hn q (varIndex r c)) =
              (List.ofFn (fun r : Fin n => if q c = (r.val : ℤ) then 1 else 0)) := by
    apply List.ext_get
    · simp
    · intro i h1 h2
      simp
      exact lift_at_varIndex hn q ⟨i, by simp at h1; exact h1⟩ c
  rw [h_eq]
  -- Step 2: Apply sum_indicator_index_eq
  have h_unique := unique_row_for_column q h_sol c
  exact sum_indicator_index_eq (q c) h_unique

/-- Extract AllDifferent constraint for negative diagonals (q[i] - i) -/
lemma extract_alldifferent_diag_neg (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) :
    ∀ c₁ c₂ : Fin n, q c₁ - (c₁.val : ℤ) = q c₂ - (c₂.val : ℤ) → c₁ = c₂ := by
  -- Extract the diagonal constraint from h_sol
  have h_mem : diagonal_constraint1D n ∈ (nqueens_csp1D n).constraints := by
    unfold nqueens_csp1D
    simp [diagonal_constraint1D]
  have h_sat' : (List.ofFn fun i : Fin n => q i - (i.val : ℤ)).Nodup :=
    (diag_neg_holds_iff _).mp (h_sol (diagonal_constraint1D n) h_mem)
  rw [List.nodup_ofFn] at h_sat'
  exact h_sat'

/-- Extract AllDifferent constraint for positive diagonals (q[i] + i) -/
lemma extract_alldifferent_diag_pos (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) :
    ∀ c₁ c₂ : Fin n, q c₁ + (c₁.val : ℤ) = q c₂ + (c₂.val : ℤ) → c₁ = c₂ := by
  -- Extract the antidiagonal constraint from h_sol
  have h_mem : antidiagonal_constraint1D n ∈ (nqueens_csp1D n).constraints := by
    unfold nqueens_csp1D
    simp [antidiagonal_constraint1D]
  have h_sat' : (List.ofFn fun i : Fin n => q i + (i.val : ℤ)).Nodup :=
    (diag_pos_holds_iff _).mp (h_sol (antidiagonal_constraint1D n) h_mem)
  rw [List.nodup_ofFn] at h_sat'
  exact h_sat'

/-- lift satisfies each diagonal constraint -/
lemma lift_satisfies_each_diagonal (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) (d : ℤ) :
    ((diag_variables d).map (lift hn q)).sum ≤ 1 := by
  by_contra h_not_le
  push Not at h_not_le
  have h_sum_ge_2 : ((diag_variables d).map (lift hn q)).sum ≥ 2 := by
    have h_gt : 1 < ((diag_variables d).map (lift hn q)).sum := h_not_le
    exact Int.add_one_le_of_lt h_gt
  have h_binary : ∀ v ∈ diag_variables d, lift hn q v = 0 ∨ lift hn q v = 1 := by
    intro v _
    exact lift_binary hn q v

  have h_exists_two : ∃ v₁ v₂ : Fin (n*n), v₁ ∈ diag_variables d ∧ v₂ ∈ diag_variables d ∧
      v₁ ≠ v₂ ∧ lift hn q v₁ = 1 ∧ lift hn q v₂ = 1 := by
    have h_nodup : (@diag_variables n d).Nodup := by
      unfold diag_variables
      exact List.Nodup.filter _ (List.nodup_finRange _)

    have h_eq_finset : ((diag_variables d).map (lift hn q)).sum =
                       (diag_variables d).toFinset.sum (fun v => lift hn q v) := by
      rw [← List.sum_toFinset _ h_nodup]

    rw [h_eq_finset] at h_sum_ge_2

    have h_card_ge_2 : ((diag_variables d).toFinset.filter (fun v => lift hn q v = 1)).card ≥ 2 := by
      have h_eq_count : (diag_variables d).toFinset.sum (fun v => lift hn q v) =
                        ((diag_variables d).toFinset.filter (fun v => lift hn q v = 1)).card := by
        have h_step1 : (diag_variables d).toFinset.sum (fun v => lift hn q v) =
                       (diag_variables d).toFinset.sum (fun v => if lift hn q v = 1 then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro v hv
          have h_bin := h_binary v (by rw [List.mem_toFinset] at hv; exact hv)
          cases h_bin with
          | inl h0 => simp [h0]
          | inr h1 => simp [h1]
        rw [h_step1]
        have h_boole := @Finset.sum_boole _ ℤ _ (fun v => lift hn q v = 1) _ (diag_variables d).toFinset
        simp only at h_boole
        exact h_boole
      rw [h_eq_count] at h_sum_ge_2
      exact Int.ofNat_le.mp h_sum_ge_2

    have h_exists : ∃ v₁ v₂, v₁ ∈ (diag_variables d).toFinset.filter (fun v => lift hn q v = 1) ∧
                             v₂ ∈ (diag_variables d).toFinset.filter (fun v => lift hn q v = 1) ∧
                             v₁ ≠ v₂ := by
      exact Finset.one_lt_card_iff.mp h_card_ge_2

    obtain ⟨v₁, v₂, h₁, h₂, hne⟩ := h_exists
    use v₁, v₂
    constructor
    · rw [Finset.mem_filter] at h₁
      rw [List.mem_toFinset] at h₁
      exact h₁.1
    constructor
    · rw [Finset.mem_filter] at h₂
      rw [List.mem_toFinset] at h₂
      exact h₂.1
    constructor
    · exact hne
    constructor
    · rw [Finset.mem_filter] at h₁
      exact h₁.2
    · rw [Finset.mem_filter] at h₂
      exact h₂.2

  obtain ⟨v₁, v₂, h₁_in, h₂_in, h_ne, h₁_lift, h₂_lift⟩ := h_exists_two

  have h₁_diag : ((v₁.val / n : ℤ) - (v₁.val % n : ℤ)) = d := by
    simp only [diag_variables, List.mem_filter] at h₁_in
    simp only [decide_eq_true_eq] at h₁_in
    exact h₁_in.2

  have h₂_diag : ((v₂.val / n : ℤ) - (v₂.val % n : ℤ)) = d := by
    simp only [diag_variables, List.mem_filter] at h₂_in
    simp only [decide_eq_true_eq] at h₂_in
    exact h₂_in.2

  let r₁ : Fin n := ⟨v₁.val / n, by rw [Nat.div_lt_iff_lt_mul hn]; exact v₁.isLt⟩
  let c₁ : Fin n := ⟨v₁.val % n, Nat.mod_lt v₁.val hn⟩
  let r₂ : Fin n := ⟨v₂.val / n, by rw [Nat.div_lt_iff_lt_mul hn]; exact v₂.isLt⟩
  let c₂ : Fin n := ⟨v₂.val % n, Nat.mod_lt v₂.val hn⟩

  have h₁_q : q c₁ = (r₁.val : ℤ) := by
    unfold lift at h₁_lift
    simp only at h₁_lift
    split at h₁_lift
    · assumption
    · norm_num at h₁_lift

  have h₂_q : q c₂ = (r₂.val : ℤ) := by
    unfold lift at h₂_lift
    simp only at h₂_lift
    split at h₂_lift
    · assumption
    · norm_num at h₂_lift

  have h₁_diff : q c₁ - (c₁.val : ℤ) = d := by
    rw [h₁_q]
    have : (r₁.val : ℤ) = v₁.val / n := by
      simp [r₁]
    rw [this]
    have : (c₁.val : ℤ) = v₁.val % n := by
      simp [c₁]
    rw [this]
    exact h₁_diag

  have h₂_diff : q c₂ - (c₂.val : ℤ) = d := by
    rw [h₂_q]
    have : (r₂.val : ℤ) = v₂.val / n := by
      simp [r₂]
    rw [this]
    have : (c₂.val : ℤ) = v₂.val % n := by
      simp [c₂]
    rw [this]
    exact h₂_diag

  have h_alldiff := extract_alldifferent_diag_neg q h_sol
  have h_eq_cols : c₁ = c₂ := by
    apply h_alldiff
    rw [h₁_diff, h₂_diff]

  have h_eq_rows : r₁ = r₂ := by
    have : q c₁ = q c₂ := by rw [h_eq_cols]
    rw [h₁_q, h₂_q] at this
    exact Fin.ext (Int.ofNat_inj.mp this)

  have h_eq_cells : v₁ = v₂ := by
    apply Fin.ext
    have h₁_val : v₁.val = r₁.val * n + c₁.val := by
      have h_div : v₁.val / n = r₁.val := by simp [r₁]
      have h_mod : v₁.val % n = c₁.val := by simp [c₁]
      exact Nat.div_add_mod v₁.val n ▸ by rw [h_div, h_mod]; ring
    have h₂_val : v₂.val = r₂.val * n + c₂.val := by
      have h_div : v₂.val / n = r₂.val := by simp [r₂]
      have h_mod : v₂.val % n = c₂.val := by simp [c₂]
      exact Nat.div_add_mod v₂.val n ▸ by rw [h_div, h_mod]; ring
    rw [h₁_val, h₂_val, h_eq_rows, h_eq_cols]

  exact h_ne h_eq_cells

/-- lift satisfies each antidiagonal constraint -/
lemma lift_satisfies_each_antidiagonal (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) (a : ℤ) :
    ((antidiag_variables a).map (lift hn q)).sum ≤ 1 := by
  by_contra h_not_le
  push Not at h_not_le
  have h_sum_ge_2 : ((antidiag_variables a).map (lift hn q)).sum ≥ 2 := by
    have h_gt : 1 < ((antidiag_variables a).map (lift hn q)).sum := h_not_le
    exact Int.add_one_le_of_lt h_gt

  have h_binary : ∀ v ∈ antidiag_variables a, lift hn q v = 0 ∨ lift hn q v = 1 := by
    intro v _
    exact lift_binary hn q v

  have h_exists_two : ∃ v₁ v₂ : Fin (n*n), v₁ ∈ antidiag_variables a ∧ v₂ ∈ antidiag_variables a ∧
      v₁ ≠ v₂ ∧ lift hn q v₁ = 1 ∧ lift hn q v₂ = 1 := by
    have h_nodup : (@antidiag_variables n a).Nodup := by
      unfold antidiag_variables
      exact List.Nodup.filter _ (List.nodup_finRange _)

    have h_eq_finset : ((antidiag_variables a).map (lift hn q)).sum =
                       (antidiag_variables a).toFinset.sum (fun v => lift hn q v) := by
      rw [← List.sum_toFinset _ h_nodup]

    rw [h_eq_finset] at h_sum_ge_2

    have h_card_ge_2 : ((antidiag_variables a).toFinset.filter (fun v => lift hn q v = 1)).card ≥ 2 := by
      have h_eq_count : (antidiag_variables a).toFinset.sum (fun v => lift hn q v) =
                        ((antidiag_variables a).toFinset.filter (fun v => lift hn q v = 1)).card := by
        have h_step1 : (antidiag_variables a).toFinset.sum (fun v => lift hn q v) =
                       (antidiag_variables a).toFinset.sum (fun v => if lift hn q v = 1 then (1 : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro v hv
          have h_bin := h_binary v (by rw [List.mem_toFinset] at hv; exact hv)
          cases h_bin with
          | inl h0 => simp [h0]
          | inr h1 => simp [h1]
        rw [h_step1]
        have h_boole := @Finset.sum_boole _ ℤ _ (fun v => lift hn q v = 1) _ (antidiag_variables a).toFinset
        simp only at h_boole
        exact h_boole
      rw [h_eq_count] at h_sum_ge_2
      exact Int.ofNat_le.mp h_sum_ge_2

    have h_exists : ∃ v₁ v₂, v₁ ∈ (antidiag_variables a).toFinset.filter (fun v => lift hn q v = 1) ∧
                             v₂ ∈ (antidiag_variables a).toFinset.filter (fun v => lift hn q v = 1) ∧
                             v₁ ≠ v₂ := by
      exact Finset.one_lt_card_iff.mp h_card_ge_2

    obtain ⟨v₁, v₂, h₁, h₂, hne⟩ := h_exists
    use v₁, v₂
    constructor
    · rw [Finset.mem_filter] at h₁
      rw [List.mem_toFinset] at h₁
      exact h₁.1
    constructor
    · rw [Finset.mem_filter] at h₂
      rw [List.mem_toFinset] at h₂
      exact h₂.1
    constructor
    · exact hne
    constructor
    · rw [Finset.mem_filter] at h₁
      exact h₁.2
    · rw [Finset.mem_filter] at h₂
      exact h₂.2

  obtain ⟨v₁, v₂, h₁_in, h₂_in, h_ne, h₁_lift, h₂_lift⟩ := h_exists_two

  have h₁_antidiag : ((v₁.val / n : ℤ) + (v₁.val % n : ℤ)) = a := by
    simp only [antidiag_variables, List.mem_filter] at h₁_in
    simp only [decide_eq_true_eq] at h₁_in
    exact h₁_in.2

  have h₂_antidiag : ((v₂.val / n : ℤ) + (v₂.val % n : ℤ)) = a := by
    simp only [antidiag_variables, List.mem_filter] at h₂_in
    simp only [decide_eq_true_eq] at h₂_in
    exact h₂_in.2

  let r₁ : Fin n := ⟨v₁.val / n, by rw [Nat.div_lt_iff_lt_mul hn]; exact v₁.isLt⟩
  let c₁ : Fin n := ⟨v₁.val % n, Nat.mod_lt v₁.val hn⟩
  let r₂ : Fin n := ⟨v₂.val / n, by rw [Nat.div_lt_iff_lt_mul hn]; exact v₂.isLt⟩
  let c₂ : Fin n := ⟨v₂.val % n, Nat.mod_lt v₂.val hn⟩

  have h₁_q : q c₁ = (r₁.val : ℤ) := by
    unfold lift at h₁_lift
    simp only at h₁_lift
    split at h₁_lift
    · assumption
    · norm_num at h₁_lift

  have h₂_q : q c₂ = (r₂.val : ℤ) := by
    unfold lift at h₂_lift
    simp only at h₂_lift
    split at h₂_lift
    · assumption
    · norm_num at h₂_lift

  have h₁_sum : q c₁ + (c₁.val : ℤ) = a := by
    rw [h₁_q]
    have : (r₁.val : ℤ) = v₁.val / n := by
      simp [r₁]
    rw [this]
    have : (c₁.val : ℤ) = v₁.val % n := by
      simp [c₁]
    rw [this]
    exact h₁_antidiag

  have h₂_sum : q c₂ + (c₂.val : ℤ) = a := by
    rw [h₂_q]
    have : (r₂.val : ℤ) = v₂.val / n := by
      simp [r₂]
    rw [this]
    have : (c₂.val : ℤ) = v₂.val % n := by
      simp [c₂]
    rw [this]
    exact h₂_antidiag

  have h_alldiff := extract_alldifferent_diag_pos q h_sol
  have h_eq_cols : c₁ = c₂ := by
    apply h_alldiff
    rw [h₁_sum, h₂_sum]

  have h_eq_rows : r₁ = r₂ := by
    have : q c₁ = q c₂ := by rw [h_eq_cols]
    rw [h₁_q, h₂_q] at this
    exact Fin.ext (Int.ofNat_inj.mp this)

  have h_eq_cells : v₁ = v₂ := by
    apply Fin.ext
    have h₁_val : v₁.val = r₁.val * n + c₁.val := by
      have h_div : v₁.val / n = r₁.val := by simp [r₁]
      have h_mod : v₁.val % n = c₁.val := by simp [c₁]
      exact Nat.div_add_mod v₁.val n ▸ by rw [h_div, h_mod]; ring
    have h₂_val : v₂.val = r₂.val * n + c₂.val := by
      have h_div : v₂.val / n = r₂.val := by simp [r₂]
      have h_mod : v₂.val % n = c₂.val := by simp [c₂]
      exact Nat.div_add_mod v₂.val n ▸ by rw [h_div, h_mod]; ring
    rw [h₁_val, h₂_val, h_eq_rows, h_eq_cols]

  exact h_ne h_eq_cells

/-- lift satisfies all diagonal and antidiagonal constraints -/
lemma lift_satisfies_diag_constraints (q : IntAssignment n)
    (h_sol : IntCSP.isSolutionInt (nqueens_csp1D n) q) :
    ∀ c ∈ diag_constraints2D n ++ antidiag_constraints2D n,
      IntCSP.satisfiesConstraintInt c (lift hn q) := by
  intro c h_mem
  rw [List.mem_append] at h_mem
  cases h_mem with
  | inl h_diag =>
    unfold diag_constraints2D at h_diag
    rw [List.mem_filterMap] at h_diag
    obtain ⟨k, _, h_some⟩ := h_diag
    simp only at h_some
    split at h_some
    · contradiction  -- cells = [], but we have some
    · have h_c : c = sum_le (listToVector (diag_variables ((k : ℤ) - (n - 1)))) 1 := by
        exact Option.some_inj.mp h_some.symm
      rw [h_c]
      rw [sum_le_holds_iff]
      exact lift_satisfies_each_diagonal hn q h_sol ((k : ℤ) - (n - 1))
  | inr h_antidiag =>
    unfold antidiag_constraints2D at h_antidiag
    rw [List.mem_filterMap] at h_antidiag
    obtain ⟨k, _, h_some⟩ := h_antidiag
    simp only at h_some
    split at h_some
    · contradiction
    · have h_c : c = sum_le (listToVector (antidiag_variables k)) 1 := by
        exact Option.some_inj.mp h_some.symm
      rw [h_c]
      rw [sum_le_holds_iff]
      exact lift_satisfies_each_antidiagonal hn q h_sol k

/-- Backward direction: 1D solution lifts to 2D solution -/
theorem backward_direction (hn : 0 < n) (sol₁ : IntAssignment n)
    (h : IntCSP.isSolutionInt (nqueens_csp1D n) sol₁) :
    ∃ sol₂ : IntAssignment (n*n),
      IntCSP.isSolutionInt (nqueens_csp2D n) sol₂ ∧ π sol₂ = sol₁ := by
  use lift hn sol₁
  constructor
  · intro c h_mem
    unfold nqueens_csp2D at h_mem
    simp [List.mem_append] at h_mem
    rcases h_mem with h_bound | h_row | h_col | h_diag | h_antidiag
    · -- Bound constraints
      simp only [bound_constraints2D, List.mem_map] at h_bound
      obtain ⟨v, _, rfl⟩ := h_bound
      show IntCSP.satisfiesConstraintInt (bound v 0 1) (lift hn sol₁)
      rw [bound_holds_iff]
      rcases lift_binary hn sol₁ v with h0 | h0 <;> rw [h0] <;> norm_num
    · -- Row constraints
      simp only [row_constraints2D, List.mem_map] at h_row
      obtain ⟨r, _, rfl⟩ := h_row
      show IntCSP.satisfiesConstraintInt (sum_eq (row_variables r) 1) (lift hn sol₁)
      rw [sum_eq_holds_iff]
      unfold row_variables
      simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
      show (List.ofFn fun c : Fin n => lift hn sol₁ (varIndex r c)).sum = 1
      exact lift_satisfies_row_constraints hn sol₁ h r
    · -- Column constraints
      simp only [col_constraints2D, List.mem_map] at h_col
      obtain ⟨c_idx, _, rfl⟩ := h_col
      show IntCSP.satisfiesConstraintInt (sum_eq (col_variables c_idx) 1) (lift hn sol₁)
      rw [sum_eq_holds_iff]
      unfold col_variables
      simp only [_root_.Vector.toList_ofFn, List.map_ofFn]
      show (List.ofFn fun r : Fin n => lift hn sol₁ (varIndex r c_idx)).sum = 1
      exact lift_satisfies_col_constraints hn sol₁ h c_idx
    · -- Diagonal constraints
      have h_combined := lift_satisfies_diag_constraints hn sol₁ h
      exact h_combined c (List.mem_append.mpr (Or.inl h_diag))
    · -- Antidiagonal constraints
      have h_combined := lift_satisfies_diag_constraints hn sol₁ h
      exact h_combined c (List.mem_append.mpr (Or.inr h_antidiag))
  · exact π_lift_inverse hn sol₁ (fun c => solution_1D_bounds sol₁ h c)

end BackwardDirection

-- ============================================================================
-- Injectivity
-- ============================================================================

section Injectivity

variable {n : ℕ} (hn : 0 < n)

/-- π is injective on solutions -/
theorem injective_on_solutions (hn : 0 < n) (sol₂ sol₂' : IntAssignment (n*n))
    (h₂ : IntCSP.isSolutionInt (nqueens_csp2D n) sol₂)
    (h₂' : IntCSP.isSolutionInt (nqueens_csp2D n) sol₂')
    (h_eq : π sol₂ = π sol₂') :
    sol₂ = sol₂' := by
  funext v
  let r : Fin n := ⟨v.val / n, by
    rw [Nat.div_lt_iff_lt_mul]
    exact v.isLt
    exact hn⟩
  let c : Fin n := ⟨v.val % n, by exact Nat.mod_lt (↑v) hn⟩
  have h_v_eq : v = varIndex r c := by
    apply Fin.ext
    unfold varIndex
    simp only
    show v.val = r.val * n + c.val
    have h_div_mod : v.val = n * (v.val / n) + v.val % n := (Nat.div_add_mod v.val n).symm
    calc v.val = n * (v.val / n) + v.val % n := h_div_mod
         _ = (v.val / n) * n + v.val % n := by rw [Nat.mul_comm]
         _ = r.val * n + c.val := by rfl
  obtain ⟨r₂, h₂_val, h₂_uniq⟩ := col_has_exactly_one sol₂ h₂ c
  obtain ⟨r₂', h₂'_val, h₂'_uniq⟩ := col_has_exactly_one sol₂' h₂' c

  have h_proj_c : π sol₂ c = π sol₂' c := congrFun h_eq c

  have h_π₂ : π sol₂ c = r₂.val := π_eq_row_of_queen sol₂ h₂ c r₂ h₂_val
  have h_π₂' : π sol₂' c = r₂'.val := π_eq_row_of_queen sol₂' h₂' c r₂' h₂'_val

  have h_r_eq : r₂ = r₂' := by
    apply Fin.ext
    have : (r₂.val : ℤ) = (r₂'.val : ℤ) := by
      rw [← h_π₂, ← h_π₂', h_proj_c]
    exact Nat.cast_injective this

  rw [h_v_eq]

  by_cases h_case : r = r₂
  · calc sol₂ (varIndex r c) = sol₂ (varIndex r₂ c) := by rw [h_case]
       _ = 1 := h₂_val
       _ = sol₂' (varIndex r₂' c) := h₂'_val.symm
       _ = sol₂' (varIndex r c) := by rw [← h_r_eq, ← h_case]
  · have h₂_zero : sol₂ (varIndex r c) = 0 := by
      have h_bound_mem : bound (varIndex r c) 0 1 ∈ (nqueens_csp2D n).constraints := by
        unfold nqueens_csp2D
        simp [bound_constraints2D, List.finRange]
      have h_bound_sat := (bound_holds_iff _ _ _ _).mp
        (h₂ (bound (varIndex r c) 0 1) h_bound_mem)
      by_cases h_val : sol₂ (varIndex r c) = 1
      · have : r = r₂ := h₂_uniq r h_val
        exact absurd this h_case
      · have h_lb := h_bound_sat.1
        have h_ub := h_bound_sat.2
        have : sol₂ (varIndex r c) < 1 := by
          exact Int.lt_iff_le_and_ne.mpr ⟨h_ub, h_val⟩
        have : sol₂ (varIndex r c) ≤ 0 := by exact Int.le_iff_lt_add_one.mpr this
        exact Int.le_antisymm this h_lb

    have h₂'_zero : sol₂' (varIndex r c) = 0 := by
      have h_bound_mem : bound (varIndex r c) 0 1 ∈ (nqueens_csp2D n).constraints := by
        unfold nqueens_csp2D
        simp [bound_constraints2D, List.finRange]
      have h_bound_sat := (bound_holds_iff _ _ _ _).mp
        (h₂' (bound (varIndex r c) 0 1) h_bound_mem)
      by_cases h_val : sol₂' (varIndex r c) = 1
      · have : r = r₂' := h₂'_uniq r h_val
        have h_r_ne_r₂' : r ≠ r₂' := by
          rw [← h_r_eq]  -- Rewrite r₂' with r₂ to get r ≠ r₂
          exact h_case
        exact absurd this h_r_ne_r₂'
      · have h_lb := h_bound_sat.1
        have h_ub := h_bound_sat.2
        have : sol₂' (varIndex r c) < 1 := by
          exact Int.lt_iff_le_and_ne.mpr ⟨h_ub, h_val⟩
        have : sol₂' (varIndex r c) ≤ 0 := by exact Int.le_iff_lt_add_one.mpr this
        exact Int.le_antisymm this h_lb

    calc sol₂ (varIndex r c) = 0 := h₂_zero
       _ = sol₂' (varIndex r c) := h₂'_zero.symm

end Injectivity

-- ============================================================================
-- π-Equivalence
-- ============================================================================

section PiEquivalence

variable {n : ℕ}

/-- N-Queens 1D and 2D formulations are π-equivalent -/
theorem nqueens_pi_equivalent (hn : 0 < n):
    piEquivalent (nqueens_csp1D n) (nqueens_csp2D n) π := by
  constructor
  · intro sol₂ h_sol₂
    exact forward_direction hn sol₂ h_sol₂
  constructor
  · intro sol₁ h_sol₁
    exact backward_direction hn sol₁ h_sol₁
  · intro sol₂ sol₂' h_sol₂ h_sol₂' h_eq
    exact injective_on_solutions hn sol₂ sol₂' h_sol₂ h_sol₂' h_eq

/-- N-Queens formulations are equivalent (strong equivalence) -/
theorem nqueens_equivalent (hn_pos : 0 < n) :
    equivalent (nqueens_csp2D n) (nqueens_csp1D n) :=
  piEquivalent_implies_equivalent _ _ _ (nqueens_pi_equivalent hn_pos)

/-- N-Queens formulations are equisatisfiable -/
theorem nqueens_equisatisfiable (hn_pos : 0 < n) :
    equisatisfiable (nqueens_csp1D n) (nqueens_csp2D n) :=
  piEquivalent_implies_equisatisfiable _ _ _ (nqueens_pi_equivalent hn_pos)

end PiEquivalence

-- ============================================================================
-- Solvers translation
-- ============================================================================


def main : IO Unit := do
  let lb := 4
  let ub := 15
  let step := 1
  let count := ((ub - lb) / step) + 1
  let sizes := (List.range count).map (fun i => lb + i * step)

  IO.println s!"Generating N-Queens instances (1D and 2D) for n={lb} to n={ub}..."

  for n in sizes do
    IO.println s!"  Generating n={n}..."

    let csp1d := nqueens_csp1D n
    let csp2d := nqueens_csp2D n

    -- Generate 1D instances
    saveToAuto csp1d s!"CSP/L2S/Proofs/mzn/nqueens_eq/enc1d_{n}" BackendType.MiniZinc
    saveToAuto csp1d s!"CSP/L2S/Proofs/smt2/nqueens_eq/enc1d_{n}" BackendType.SMTLIB

    -- Generate SBC instances
    saveToAuto csp2d s!"CSP/L2S/Proofs/mzn/nqueens_eq/enc2d_{n}" BackendType.MiniZinc
    saveToAuto csp2d s!"CSP/L2S/Proofs/smt2/nqueens_eq/enc2d_{n}" BackendType.SMTLIB


  IO.println s!"✓ Generated N-Queens instances for n={lb} to n={ub}"
