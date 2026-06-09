import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Translate
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

open CSP.L2S

/-!
## Graph Coloring Equivalent Formulations

### Formulation 1 (Vertex Model)
Variables: One per vertex (|V|)
Domains: Colors {0, 1, ..., k-1}
Constraints: Adjacent vertices have different colors

### Formulation 2 (Binary Matrix Model)
Variables: One per (vertex, color) pair (|V| × k)
Domain: {0, 1} (binary)
Constraints:
- Each vertex assigned exactly one color (one-hot encoding)
- Adjacent vertices cannot share a color

### π-Equivalence
We prove these formulations are π-equivalent via:
- Projection π: Matrix → Vertex (extract color from one-hot encoding)
- Lifting λ: Vertex → Matrix (construct one-hot encoding)
-/

-- ============================================================================
-- CSP Definitions
-- ============================================================================

section Definitions

variable (vertices colors : ℕ) (edges : List (Fin vertices × Fin vertices))

-- Formulation 1: Vertex Model

/-- Bounds: each vertex has a color in {0, ..., colors-1} -/
def vertex_bounds_1 : List (IntConstraint vertices) :=
  (List.finRange vertices).map (fun v => bound v 0 (colors-1))

/-- Edge constraints: adjacent vertices have different colors -/
def edge_constraints_1 (edges : List (Fin vertices × Fin vertices)) : List (IntConstraint vertices) :=
  edges.map (fun (u, v) => not_equal u v)

/-- Vertex model CSP -/
def graph_coloring_vertex (vertices colors : ℕ) (edges : List (Fin vertices × Fin vertices)) : IntCSP :=
  ⟨ vertices,
    vertex_bounds_1 vertices colors ++ edge_constraints_1 vertices edges ⟩

-- Formulation 2: Binary Matrix Model

/-- Helper: index for cell (vertex v, color c) in flattened matrix -/
def matrixIndex (v : Fin vertices) (c : Fin colors) : Fin (vertices * colors) :=
  ⟨v.val * colors + c.val, by
    have h1 : v.val < vertices := v.isLt
    have h2 : c.val < colors := c.isLt
    calc v.val * colors + c.val
        < v.val * colors + colors := Nat.add_lt_add_left h2 _
      _ = (v.val + 1) * colors := by ring
      _ ≤ vertices * colors := Nat.mul_le_mul_right colors (Nat.succ_le_of_lt h1)⟩

/-- Helper: get all variables for a vertex (row in matrix) -/
def vertex_colors (v : Fin vertices) : _root_.Vector (VarType (vertices * colors)) colors :=
  _root_.Vector.ofFn (fun c => matrixIndex vertices colors v c)

/-- Bounds: all matrix entries are binary {0, 1} -/
def matrix_bounds_2 : List (IntConstraint (vertices * colors)) :=
  (List.finRange (vertices * colors)).map (fun idx => bound idx 0 1)

/-- One-hot constraint: each vertex has exactly one color -/
def one_hot_constraints_2 : List (IntConstraint (vertices * colors)) :=
  (List.finRange vertices).map (fun v => sum_eq (vertex_colors vertices colors v) 1)

/-- Edge constraints: for each edge (u,v) and color c, at most one of u or v can have color c -/
def edge_matrix_constraints_2 (edges : List (Fin vertices × Fin vertices)) : List (IntConstraint (vertices * colors)) :=
  edges.flatMap fun (u, v) =>
    (List.finRange colors).map fun c =>
      let u_c := matrixIndex vertices colors u c
      let v_c := matrixIndex vertices colors v c
      let scope := ⟨#[u_c, v_c], rfl⟩
      sum_le scope 1

/-- Binary matrix model CSP -/
def graph_coloring_matrix (vertices colors : ℕ)
    (edges : List (Fin vertices × Fin vertices)) : IntCSP :=
  ⟨ vertices * colors,
    matrix_bounds_2 vertices colors ++
    one_hot_constraints_2 vertices colors ++
    edge_matrix_constraints_2 vertices colors edges ⟩

end Definitions

-- ============================================================================
-- Projection and Lifting Functions
-- ============================================================================

-- No section here, define at top level

/--
Projection π: Matrix → Vertex
For each vertex v, find the unique color c where matrix[v,c] = 1
-/
def π {vertices colors : ℕ} (x : IntAssignment (vertices * colors)) : IntAssignment vertices :=
  fun v : Fin vertices =>
    match (List.finRange colors).find? (fun c =>
      x (matrixIndex vertices colors v c) = 1) with
    | some c => c.val
    | none => 0  -- default (should not occur for valid solutions)

/--
Lifting lift: Vertex → Matrix
Set matrix[v,c] = 1 iff vertex_color(v) = c
-/
def lift {vertices colors : ℕ} (h_colors : 0 < colors) (assignment : IntAssignment vertices) :
    IntAssignment (vertices * colors) :=
  fun idx : Fin (vertices * colors) =>
    let c : Fin colors := ⟨idx.val % colors, Nat.mod_lt idx.val h_colors⟩
    if assignment ⟨(idx.val / colors), by
      rw [Nat.div_lt_iff_lt_mul h_colors]
      exact idx.isLt⟩ = c.val then 1 else 0

-- ============================================================================
-- Auxiliary Lemmas
-- ============================================================================

section AuxiliaryLemmas

variable {vertices colors : ℕ} (h_colors : 0 < colors) (edges : List (Fin vertices × Fin vertices))

/-- Matrix index division gives the vertex -/
lemma matrixIndex_div_eq (v : Fin vertices) (c : Fin colors) :
    (matrixIndex vertices colors v c).val / colors = v.val := by
  unfold matrixIndex
  simp only
  have h_c : c.val < colors := c.isLt
  have h_c_div_zero : c.val / colors = 0 := Nat.div_eq_zero_iff.mpr (Or.inr h_c)
  have h_colors_pos : 0 < colors := Fin.pos c
  rw [Nat.add_comm, Nat.mul_comm]
  rw [Nat.add_mul_div_left _ _ h_colors_pos]
  rw [h_c_div_zero]
  omega

/-- Matrix index modulo gives the color -/
lemma matrixIndex_mod_eq (v : Fin vertices) (c : Fin colors) :
    (matrixIndex vertices colors v c).val % colors = c.val := by
  unfold matrixIndex
  simp only
  refine Nat.mul_add_mod_of_lt ?_
  exact c.isLt

/-- π∘lift is the identity (for valid vertex colorings) -/
lemma π_lift_inverse (assignment : IntAssignment vertices)
    (h_bounds : ∀ v : Fin vertices, 0 ≤ assignment v ∧ assignment v < colors) :
    π (lift h_colors assignment) = assignment := by
  funext v
  unfold π
  have h_v := h_bounds v
  have h_toNat_eq : ((assignment v).toNat : ℤ) = assignment v := by
    have h_nonneg : 0 ≤ assignment v := h_v.1
    exact Int.toNat_of_nonneg h_nonneg
  let c_target : Fin colors := ⟨(assignment v).toNat, by
    have h_lt : assignment v < colors := h_v.2
    have h_nonneg : 0 ≤ assignment v := h_v.1
    exact (Int.toNat_lt h_nonneg).mpr h_lt⟩

  have h_find : (List.finRange colors).find? (fun c =>
      (lift h_colors assignment) (matrixIndex vertices colors v c) = 1) = some c_target := by
    have h_eq : List.finRange colors = List.ofFn id := rfl
    rw [h_eq]
    have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin colors) colors id
      (fun c => decide ((lift h_colors assignment) (matrixIndex vertices colors v c) = 1))
      c_target Function.injective_id
    simp only [id_eq] at h_lem
    rw [h_lem]
    constructor
    · simp only [decide_eq_true_eq]
      unfold lift
      have h_mod := matrixIndex_mod_eq v c_target
      have h_div := matrixIndex_div_eq v c_target
      simp only [h_mod, ite_eq_left_iff]
      intro h_ne
      exfalso
      apply h_ne
      have : assignment v = (c_target.val : ℤ) := by
        simp [c_target, h_toNat_eq]
      have h_v_fin : ⟨(matrixIndex vertices colors v c_target).val / colors, by
        rw [h_div]
        exact v.isLt⟩ = v := by
        simp [h_div]
      rw [h_v_fin]
      exact this
    · intro c' h_c'_lt
      simp only [decide_eq_true_eq]
      unfold lift
      have h_mod := matrixIndex_mod_eq v c'
      have h_div := matrixIndex_div_eq v c'
      simp only [h_mod]
      intro h_eq
      have h_target_eq : assignment v = (c_target.val : ℤ) := by
        simp [c_target, h_toNat_eq]
      have h_v_fin : ⟨(matrixIndex vertices colors v c').val / colors, by
        rw [h_div]; exact v.isLt⟩ = v := by
        ext; simp [h_div]
      rw [h_v_fin] at h_eq
      have h_cond : assignment v = (c'.val : ℤ) := by
        by_contra h_ne
        simp [h_ne] at h_eq
      have : (c'.val : ℤ) = (c_target.val : ℤ) := by
        rw [← h_cond, h_target_eq]
      have : c'.val = c_target.val := by omega
      have : c' = c_target := Fin.ext this
      omega
  rw [h_find]
  simp
  rw [← h_toNat_eq]

/-- A matrix solution has exactly one color per vertex -/
lemma matrix_one_hot (x : IntAssignment (vertices * colors))
    (h_sol : IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) x)
    (v : Fin vertices) :
    ∃! c : Fin colors, x (matrixIndex vertices colors v c) = 1 := by
  have h_mem : sum_eq (vertex_colors vertices colors v) 1 ∈
      (graph_coloring_matrix vertices colors edges).constraints := by
    unfold graph_coloring_matrix
    simp [one_hot_constraints_2, List.finRange]
  have h_sat := h_sol (sum_eq (vertex_colors vertices colors v) 1) h_mem
  unfold IntCSP.satisfiesConstraintInt at h_sat
  unfold sum_eq sum_rel at h_sat
  unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint at h_sat
  unfold CSP.map_assignment at h_sat
  simp [CSP.sat, extractValues] at h_sat
  have h_binary : ∀ c : Fin colors, x (matrixIndex vertices colors v c) = 0 ∨ x (matrixIndex vertices colors v c) = 1 := by
    intro c
    have h_bound_mem : bound (matrixIndex vertices colors v c) 0 1 ∈
        (graph_coloring_matrix vertices colors edges).constraints := by
      unfold graph_coloring_matrix
      simp [matrix_bounds_2, List.finRange]
    have h_bound_sat := h_sol (bound (matrixIndex vertices colors v c) 0 1) h_bound_mem
    unfold IntCSP.satisfiesConstraintInt at h_bound_sat
    unfold bound at h_bound_sat
    unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint at h_bound_sat
    unfold CSP.map_assignment at h_bound_sat
    simp [CSP.sat, extractValues, _root_.Vector.get] at h_bound_sat
    have h_lb := h_bound_sat.1
    have h_ub := h_bound_sat.2
    by_cases h_eq_zero : x (matrixIndex vertices colors v c) = 0
    · left; exact h_eq_zero
    · right
      have h_pos : 0 < x (matrixIndex vertices colors v c) := by
        have : 0 ≠ x (matrixIndex vertices colors v c) := by exact fun a => h_eq_zero (id (Eq.symm a))
        exact Std.lt_of_le_of_ne h_lb this
      have : x (matrixIndex vertices colors v c) = 1 := by
        exact Eq.symm (Int.le_antisymm h_pos h_ub)
      exact this
  have h_sum_matrixIndex : (List.ofFn fun c : Fin colors => x (matrixIndex vertices colors v c)).sum = 1 := by
    have vget : ∀ {α : Type} {m : ℕ} (f : Fin m → α) (k : Fin m),
        (_root_.Vector.ofFn f).get k = f k := by
      intro α m f k
      simp only [_root_.Vector.get, _root_.Vector.toArray_ofFn, Array.getElem_ofFn,
        Fin.val_cast, Fin.eta]
    convert h_sat using 3 with i
    funext i
    exact congrArg x (vget (fun c => matrixIndex vertices colors v c) i).symm

  have h_exists : ∃ c : Fin colors, x (matrixIndex vertices colors v c) = 1 := by
    by_contra h_none
    push_neg at h_none
    have h_all_zero : ∀ c : Fin colors, x (matrixIndex vertices colors v c) = 0 := by
      intro c
      cases h_binary c with
      | inl h => exact h
      | inr h => exact absurd h (h_none c)
    have h_sum_zero : (List.ofFn fun c : Fin colors => x (matrixIndex vertices colors v c)).sum = 0 := by
      have : (fun c : Fin colors => x (matrixIndex vertices colors v c)) = (fun _ => 0) := by
        funext c
        exact h_all_zero c
      simp [this]
    rw [h_sum_zero] at h_sum_matrixIndex
    norm_num at h_sum_matrixIndex

  have h_unique : ∀ c₁ c₂ : Fin colors,
      x (matrixIndex vertices colors v c₁) = 1 → x (matrixIndex vertices colors v c₂) = 1 → c₁ = c₂ := by
    intro c₁ c₂ h₁ h₂
    by_contra h_ne
    have h_two : x (matrixIndex vertices colors v c₁) + x (matrixIndex vertices colors v c₂) = 2 := by
      rw [h₁, h₂]; norm_num
    have h_nonneg : ∀ c : Fin colors, 0 ≤ x (matrixIndex vertices colors v c) := by
      intro c
      cases h_binary c with
      | inl h => rw [h]
      | inr h => rw [h]; norm_num
    have h_sum_ge_2 : (List.ofFn fun c : Fin colors => x (matrixIndex vertices colors v c)).sum ≥ 2 := by
      have h_eq_finset : (List.ofFn fun c : Fin colors => x (matrixIndex vertices colors v c)).sum =
                         (Finset.univ : Finset (Fin colors)).sum (fun c => x (matrixIndex vertices colors v c)) := by
        have : (List.ofFn fun c : Fin colors => x (matrixIndex vertices colors v c)) =
               List.map (fun c => x (matrixIndex vertices colors v c)) (List.finRange colors) := by
          rw [List.ofFn_eq_map]
        rw [this]
        rw [← List.sum_toFinset _ (List.nodup_finRange colors)]
        congr 1
        exact List.toFinset_finRange colors
      rw [h_eq_finset]
      have h_decomp : (Finset.univ : Finset (Fin colors)).sum (fun c => x (matrixIndex vertices colors v c)) =
                      x (matrixIndex vertices colors v c₁) + x (matrixIndex vertices colors v c₂) +
                      ((Finset.univ : Finset (Fin colors)) \ {c₁, c₂}).sum (fun c => x (matrixIndex vertices colors v c)) := by
        rw [← Finset.sum_sdiff (Finset.subset_univ {c₁, c₂})]
        have h_pair_sum : ({c₁, c₂} : Finset (Fin colors)).sum (fun c => x (matrixIndex vertices colors v c)) =
                          x (matrixIndex vertices colors v c₁) + x (matrixIndex vertices colors v c₂) := by
          rw [Finset.sum_pair h_ne]
        rw [h_pair_sum, add_comm]
      rw [h_decomp]
      have h_rest_nonneg : 0 ≤ ((Finset.univ : Finset (Fin colors)) \ {c₁, c₂}).sum
          (fun c => x (matrixIndex vertices colors v c)) := by
        apply Finset.sum_nonneg
        intros c _
        exact h_nonneg c
      calc x (matrixIndex vertices colors v c₁) + x (matrixIndex vertices colors v c₂) +
           ((Finset.univ : Finset (Fin colors)) \ {c₁, c₂}).sum (fun c => x (matrixIndex vertices colors v c))
          ≥ x (matrixIndex vertices colors v c₁) + x (matrixIndex vertices colors v c₂) + 0 := by linarith
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

/-- A vertex solution has valid color bounds -/
lemma vertex_solution_bounds (assignment : IntAssignment vertices)
    (h_sol : IntCSP.isSolutionInt (graph_coloring_vertex vertices colors edges) assignment)
    (v : Fin vertices) :
    0 ≤ assignment v ∧ assignment v < colors := by
  have h_mem : bound v 0 (colors-1) ∈ (graph_coloring_vertex vertices colors edges).constraints := by
    unfold graph_coloring_vertex
    simp only [List.mem_append]
    left
    unfold vertex_bounds_1
    simp only [List.mem_map, List.mem_finRange, true_and]
    use v
  have h_sat := h_sol (bound v 0 (colors-1)) h_mem
  unfold IntCSP.satisfiesConstraintInt at h_sat
  unfold bound at h_sat
  unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint at h_sat
  unfold CSP.map_assignment at h_sat
  simp [CSP.sat, extractValues, _root_.Vector.get] at h_sat
  constructor
  · exact h_sat.1
  · have h_ub : assignment v ≤ (colors : ℤ) - 1 := h_sat.2
    have h_colors_pos : 0 < (colors : ℤ) := by omega
    linarith

end AuxiliaryLemmas

-- ============================================================================
-- Main Theorems
-- ============================================================================

section MainTheorems

variable {vertices colors : ℕ} (h_colors : 0 < colors) (edges : List (Fin vertices × Fin vertices))

/-- Forward direction: matrix solution projects to vertex solution -/
theorem forward (sol₂ : IntAssignment (vertices * colors))
    (h_sol₂ : IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂) :
    IntCSP.isSolutionInt (graph_coloring_vertex vertices colors edges) (π sol₂) := by
  unfold IntCSP.isSolutionInt
  intro c h_c
  unfold graph_coloring_vertex at h_c
  simp only [List.mem_append] at h_c
  rcases h_c with h_bounds | h_edges
  · obtain ⟨v, ⟨_, h_eq⟩⟩ := (List.mem_map.mp h_bounds)
    subst h_eq
    unfold IntCSP.satisfiesConstraintInt bound
    unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.map_assignment
    simp [CSP.sat, extractValues, _root_.Vector.get]
    unfold π
    have h_one_hot : ∃! c : Fin colors, sol₂ (matrixIndex vertices colors v c) = 1 := by
      apply matrix_one_hot
      exact h_sol₂
    have ⟨c_wit, h_wit, h_unique⟩ := h_one_hot
    constructor
    · split
      · exact Int.natCast_nonneg _
      · omega
    · split
      next c h_some =>
        have : c.val < colors := c.isLt
        omega
      next h_none =>
        have : 0 < colors := Fin.pos c_wit
        omega
  · obtain ⟨edge, ⟨h_edge_mem, h_eq⟩⟩ := (List.mem_map.mp h_edges)
    subst h_eq
    obtain ⟨u, v⟩ := edge
    unfold IntCSP.satisfiesConstraintInt not_equal
    unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.map_assignment
    simp [CSP.sat, _root_.Vector.get, CSP.binary_dynamic_constraint, CSP.binary_constraint]
    intro h_eq
    have h_one_hot_u : ∃! c : Fin colors, sol₂ (matrixIndex vertices colors u c) = 1 := by
      apply matrix_one_hot
      exact h_sol₂
    have h_one_hot_v : ∃! c : Fin colors, sol₂ (matrixIndex vertices colors v c) = 1 := by
      apply matrix_one_hot
      exact h_sol₂
    obtain ⟨c_u, h_u_wit, h_u_unique⟩ := h_one_hot_u
    obtain ⟨c_v, h_v_wit, h_v_unique⟩ := h_one_hot_v
    have h_c_ne : c_u ≠ c_v := by
      intro h_c_eq
      have h_constr : sum_le ⟨#[matrixIndex vertices colors u c_u, matrixIndex vertices colors v c_u], rfl⟩ 1 ∈
          (graph_coloring_matrix vertices colors edges).constraints := by
        unfold graph_coloring_matrix edge_matrix_constraints_2
        simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and, Prod.exists]
        right
        use u, v, h_edge_mem, c_u
      have h_sat := h_sol₂ _ h_constr
      unfold IntCSP.satisfiesConstraintInt sum_le sum_rel at h_sat
      simp only [CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat, extractValues, decide_eq_true_iff] at h_sat
      -- Reduce h_sat's sum directly to a numeric value, then derive 2 ≤ 1.
      simp only [List.ofFn, CSP.map_assignment, _root_.Vector.get] at h_sat
      change ([sol₂ (matrixIndex vertices colors u c_u),
          sol₂ (matrixIndex vertices colors v c_u)]).sum ≤ 1 at h_sat
      rw [List.sum_cons, List.sum_cons, List.sum_nil, add_zero] at h_sat
      rw [h_u_wit, h_c_eq, h_v_wit] at h_sat
      linarith
    unfold π at h_eq
    apply h_c_ne
    apply Fin.ext

    have h_find_u : (List.finRange colors).find? (fun c => sol₂ (matrixIndex vertices colors u c) = 1) = some c_u := by
      have h_eq_list : List.finRange colors = List.ofFn id := rfl
      rw [h_eq_list]
      have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin colors) colors id
        (fun c => decide (sol₂ (matrixIndex vertices colors u c) = 1))
        c_u Function.injective_id
      simp only [id_eq] at h_lem
      rw [h_lem]
      constructor
      · simp only [decide_eq_true_eq]
        exact h_u_wit
      · intro c' h_c'_lt
        simp only [decide_eq_true_eq]
        intro h_c'_sat
        have h_eq : c' = c_u := h_u_unique c' h_c'_sat
        rw [h_eq] at h_c'_lt
        exact Nat.lt_irrefl c_u.val h_c'_lt

    have h_find_v : (List.finRange colors).find? (fun c => sol₂ (matrixIndex vertices colors v c) = 1) = some c_v := by
      have h_eq_list : List.finRange colors = List.ofFn id := rfl
      rw [h_eq_list]
      have h_lem := @List.find?_ofFn_eq_some_of_injective (Fin colors) colors id
        (fun c => decide (sol₂ (matrixIndex vertices colors v c) = 1))
        c_v Function.injective_id
      simp only [id_eq] at h_lem
      rw [h_lem]
      constructor
      · simp only [decide_eq_true_eq]
        exact h_v_wit
      · intro c' h_c'_lt
        simp only [decide_eq_true_eq]
        intro h_c'_sat
        have h_eq : c' = c_v := h_v_unique c' h_c'_sat
        rw [h_eq] at h_c'_lt
        exact Nat.lt_irrefl c_v.val h_c'_lt
    -- Compute the projection of each endpoint from its unique winning color.
    have h_pi_u : π sol₂ u = (c_u.val : ℤ) := by
      unfold π
      simp [h_find_u]
    have h_pi_v : π sol₂ v = (c_v.val : ℤ) := by
      unfold π
      simp [h_find_v]
    -- The second endpoint `#[u, v][1 % #[u, v].size]` is definitionally `v`.
    have h_eq' : π sol₂ u = π sol₂ v := h_eq
    rw [h_pi_u, h_pi_v] at h_eq'
    have h_cast : (c_u.val : ℤ) = (c_v.val : ℤ) := h_eq'
    exact Nat.cast_injective h_cast

/-- Backward direction: vertex solution lifts to matrix solution -/
theorem backward (h_pos : 0 < colors) (sol₁ : IntAssignment vertices)
    (h_sol₁ : IntCSP.isSolutionInt (graph_coloring_vertex vertices colors edges) sol₁) :
    ∃ sol₂ : IntAssignment (vertices * colors),
      IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂ ∧
      π sol₂ = sol₁ := by
  let sol₂ := lift h_pos sol₁
  use sol₂
  constructor
  · unfold IntCSP.isSolutionInt
    intro c h_c
    unfold graph_coloring_matrix at h_c
    unfold matrix_bounds_2 one_hot_constraints_2 edge_matrix_constraints_2 at h_c
    simp only [List.mem_append, List.mem_map, List.mem_finRange, List.mem_flatMap, true_and, Prod.exists] at h_c
    rcases h_c with (⟨idx, h_eq⟩ | ⟨v, h_eq⟩) | ⟨u, v, h_edge_mem, color, h_eq⟩
    · subst h_eq
      unfold IntCSP.satisfiesConstraintInt bound
      unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.map_assignment
      simp [CSP.sat, extractValues, _root_.Vector.get]
      show 0 ≤ sol₂ idx ∧ sol₂ idx ≤ 1
      unfold sol₂ lift
      simp only
      split_ifs
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
    · subst h_eq
      unfold IntCSP.satisfiesConstraintInt sum_eq sum_rel
      unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint
      simp [CSP.sat, extractValues]
      have h_v_bounds := vertex_solution_bounds edges sol₁ h_sol₁ v
      have h_v_nonneg : 0 ≤ sol₁ v := h_v_bounds.1
      have h_v_lt : sol₁ v < colors := h_v_bounds.2
      have h_toNat_eq : ((sol₁ v).toNat : ℤ) = sol₁ v := Int.toNat_of_nonneg h_v_nonneg
      let c_target : Fin colors := ⟨(sol₁ v).toNat, by
        exact (Int.toNat_lt h_v_nonneg).mpr h_v_lt⟩
      show (List.ofFn fun i => sol₂ ((vertex_colors vertices colors v).get i)).sum = 1
      have h_eq : (List.ofFn fun i => sol₂ ((vertex_colors vertices colors v).get i)) =
                  (List.ofFn fun c : Fin colors => sol₂ (matrixIndex vertices colors v c)) := by
        congr 1
        funext c
        simp [vertex_colors, _root_.Vector.get, _root_.Vector.ofFn]
      rw [h_eq]
      have h_term : ∀ c : Fin colors, sol₂ (matrixIndex vertices colors v c) =
          if c.val = (sol₁ v).toNat then (1 : ℤ) else 0 := by
        intro c
        unfold sol₂ lift
        have h_div : (matrixIndex vertices colors v c).val / colors = v.val := matrixIndex_div_eq v c
        have h_mod : (matrixIndex vertices colors v c).val % colors = c.val := matrixIndex_mod_eq v c
        simp only [h_mod]
        have h_vertex_eq : (⟨(matrixIndex vertices colors v c).val / colors, by
          rw [Nat.div_lt_iff_lt_mul h_pos]
          exact (matrixIndex vertices colors v c).isLt⟩ : Fin vertices) = v := by
          ext; exact h_div
        rw [h_vertex_eq]
        have h_cast_eq : sol₁ v = ↑c.val ↔ c.val = (sol₁ v).toNat := by
          constructor
          · intro h
            have : Int.toNat (sol₁ v) = Int.toNat (↑c.val : ℤ) := by rw [h]
            rw [this, Int.toNat_natCast]
          · intro h
            calc sol₁ v = ↑(Int.toNat (sol₁ v)) := h_toNat_eq.symm
                 _      = ↑c.val := by rw [h]
        by_cases h : sol₁ v = ↑c.val
        · rw [if_pos h, if_pos (h_cast_eq.mp h)]
        · rw [if_neg h, if_neg (mt h_cast_eq.mpr h)]
      simp only [h_term]
      have h_c_target_val : c_target.val = (sol₁ v).toNat := rfl
      have h_c_target_unique : ∀ c : Fin colors, c.val = (sol₁ v).toNat → c = c_target := by
        intro c h_eq
        ext
        rw [h_eq, h_c_target_val]
      trans ((List.ofFn fun c : Fin colors => if c = c_target then (1 : ℤ) else 0).sum)
      · congr 1
        have h_fn_eq : (fun c : Fin colors => if c.val = (sol₁ v).toNat then (1 : ℤ) else 0) =
                       (fun c : Fin colors => if c = c_target then (1 : ℤ) else 0) := by
          funext c
          by_cases h : c.val = (sol₁ v).toNat
          · rw [if_pos h, if_pos (h_c_target_unique c h)]
          · rw [if_neg h]
            have : c ≠ c_target := fun h_eq => h (by rw [h_eq, h_c_target_val])
            rw [if_neg this]
        rw [h_fn_eq]
      · have h_eq_finset : (List.ofFn fun c : Fin colors => if c = c_target then (1 : ℤ) else 0).sum =
                           ∑ c : Fin colors, if c = c_target then (1 : ℤ) else 0 := by
          rw [List.sum_ofFn]
        rw [h_eq_finset]
        rw [Finset.sum_eq_single c_target]
        · simp
        · intro b _ h_ne
          simp [h_ne]
        · intro h_mem
          exfalso
          exact h_mem (Finset.mem_univ c_target)
    · subst h_eq
      unfold IntCSP.satisfiesConstraintInt sum_le sum_rel
      unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint
      simp [CSP.sat, extractValues]
      simp only [_root_.Vector.get]
      show sol₂ (matrixIndex vertices colors u color) + sol₂ (matrixIndex vertices colors v color) ≤ 1
      unfold sol₂ lift
      simp only
      have h_u_div : (matrixIndex vertices colors u color).val / colors = u.val := matrixIndex_div_eq u color
      have h_u_mod : (matrixIndex vertices colors u color).val % colors = color.val := matrixIndex_mod_eq u color
      have h_v_div : (matrixIndex vertices colors v color).val / colors = v.val := matrixIndex_div_eq v color
      have h_v_mod : (matrixIndex vertices colors v color).val % colors = color.val := matrixIndex_mod_eq v color
      have h_u_fin : (⟨(matrixIndex vertices colors u color).val / colors, by
        rw [h_u_div]; exact u.isLt⟩ : Fin vertices) = u := by
        ext; exact h_u_div
      have h_v_fin : (⟨(matrixIndex vertices colors v color).val / colors, by
        rw [h_v_div]; exact v.isLt⟩ : Fin vertices) = v := by
        ext; exact h_v_div
      simp only [h_u_fin, h_v_fin, h_u_mod, h_v_mod]
      split_ifs with h_u h_v
      · exfalso
        have h_u_eq_v : sol₁ u = sol₁ v := by
          calc sol₁ u = (color.val : ℤ) := h_u
            _ = sol₁ v := h_v.symm
        have h_edge_constr : not_equal u v ∈ (graph_coloring_vertex vertices colors edges).constraints := by
          unfold graph_coloring_vertex edge_constraints_1
          simp only [List.mem_append, List.mem_map]
          right
          use (u, v)
        have h_sat_edge := h_sol₁ (not_equal u v) h_edge_constr
        unfold IntCSP.satisfiesConstraintInt not_equal at h_sat_edge
        unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint CSP.map_assignment at h_sat_edge
        simp [CSP.sat, _root_.Vector.get, CSP.binary_dynamic_constraint, CSP.binary_constraint] at h_sat_edge
        exact h_sat_edge h_u_eq_v
      · norm_num
      · norm_num
      · norm_num
  · have h_bounds : ∀ v : Fin vertices, 0 ≤ sol₁ v ∧ sol₁ v < colors := by
      intro v
      apply vertex_solution_bounds
      exact h_sol₁
    have := π_lift_inverse h_pos sol₁ h_bounds
    exact this

/-- Injectivity: different matrix solutions with same projection are equal -/
theorem injective (h_pos : 0 < colors) (sol₂ sol₂' : IntAssignment (vertices * colors))
    (h_sol₂ : IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂)
    (h_sol₂' : IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂')
    (h_proj_eq : π sol₂ = π sol₂') :
    sol₂ = sol₂' := by
  funext idx
  let v : Fin vertices := ⟨idx.val / colors, by
    rw [Nat.div_lt_iff_lt_mul h_pos]
    exact idx.isLt⟩
  let c : Fin colors := ⟨idx.val % colors, Nat.mod_lt idx.val h_pos⟩

  have h_idx_eq : idx = matrixIndex vertices colors v c := by
    apply Fin.ext
    unfold matrixIndex
    simp only
    show idx.val = v.val * colors + c.val
    have h_div_mod : idx.val = colors * (idx.val / colors) + idx.val % colors :=
      (Nat.div_add_mod idx.val colors).symm
    calc idx.val = colors * (idx.val / colors) + idx.val % colors := h_div_mod
         _ = (idx.val / colors) * colors + idx.val % colors := by rw [Nat.mul_comm]
         _ = v.val * colors + c.val := by rfl

  have h_one_hot₂ : ∃! c : Fin colors, sol₂ (matrixIndex vertices colors v c) = 1 := by
    apply matrix_one_hot
    exact h_sol₂
  have h_one_hot₂' : ∃! c : Fin colors, sol₂' (matrixIndex vertices colors v c) = 1 := by
    apply matrix_one_hot
    exact h_sol₂'

  obtain ⟨c₂, h₂_wit, h₂_uniq⟩ := h_one_hot₂
  obtain ⟨c₂', h₂'_wit, h₂'_uniq⟩ := h_one_hot₂'

  have h_proj_v : π sol₂ v = π sol₂' v := congrFun h_proj_eq v

  have h_π₂ : π sol₂ v = ↑(c₂.val) := by
    unfold π
    have h_find : List.find? (fun c => sol₂ (matrixIndex vertices colors v c) = 1) (List.finRange colors) = some c₂ := by

      rw [List.finRange]
      have h_id : (fun i : Fin colors => i) = id := rfl
      rw [h_id]
      show List.find? (fun c => sol₂ (matrixIndex vertices colors v c) = 1) (List.ofFn id) = some (id c₂)
      rw [List.find?_ofFn_eq_some_of_injective (f := id) (p := fun c => sol₂ (matrixIndex vertices colors v c) = 1)]
      constructor
      · simp [h₂_wit]
      · intro j h_lt
        simp
        intro h_contra
        have : j = c₂ := h₂_uniq j h_contra
        rw [this] at h_lt
        exact Nat.lt_irrefl c₂.val h_lt
      · exact fun _ _ => id
    simp [h_find]

  have h_π₂' : π sol₂' v = ↑(c₂'.val) := by
    unfold π
    have h_find' : List.find? (fun c => sol₂' (matrixIndex vertices colors v c) = 1) (List.finRange colors) = some c₂' := by
      rw [List.finRange]
      have h_id : (fun i : Fin colors => i) = id := rfl
      rw [h_id]
      show List.find? (fun c => sol₂' (matrixIndex vertices colors v c) = 1) (List.ofFn id) = some (id c₂')
      rw [List.find?_ofFn_eq_some_of_injective (f := id) (p := fun c => sol₂' (matrixIndex vertices colors v c) = 1)]
      constructor
      · simp [h₂'_wit]
      · intro j h_lt
        simp
        intro h_contra
        have : j = c₂' := h₂'_uniq j h_contra
        rw [this] at h_lt
        exact Nat.lt_irrefl c₂'.val h_lt
      · exact fun _ _ => id
    simp [h_find']

  have h_c_eq : c₂ = c₂' := by
    apply Fin.ext
    have : (c₂.val : ℤ) = (c₂'.val : ℤ) := by
      rw [← h_π₂, ← h_π₂', h_proj_v]
    exact Nat.cast_injective this

  rw [h_idx_eq]

  by_cases h_case : c = c₂
  · calc sol₂ (matrixIndex vertices colors v c)
        = sol₂ (matrixIndex vertices colors v c₂) := by rw [h_case]
      _ = 1 := h₂_wit
      _ = sol₂' (matrixIndex vertices colors v c₂') := h₂'_wit.symm
      _ = sol₂' (matrixIndex vertices colors v c) := by rw [← h_c_eq, ← h_case]

  · have h₂_zero : sol₂ (matrixIndex vertices colors v c) = 0 := by
      have h_bound_mem : bound (matrixIndex vertices colors v c) 0 1 ∈
          (graph_coloring_matrix vertices colors edges).constraints := by
        unfold graph_coloring_matrix
        simp [matrix_bounds_2, List.finRange]
      have h_bound_sat := h_sol₂ (bound (matrixIndex vertices colors v c) 0 1) h_bound_mem
      unfold IntCSP.satisfiesConstraintInt at h_bound_sat
      unfold bound at h_bound_sat
      unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint at h_bound_sat
      unfold CSP.map_assignment at h_bound_sat
      simp [CSP.sat, extractValues, _root_.Vector.get] at h_bound_sat
      by_cases h_val : sol₂ (matrixIndex vertices colors v c) = 1
      · have : c = c₂ := h₂_uniq c h_val
        exact absurd this h_case
      · have h_lb := h_bound_sat.1
        have h_ub := h_bound_sat.2
        have : sol₂ (matrixIndex vertices colors v c) < 1 :=
          Int.lt_iff_le_and_ne.mpr ⟨h_ub, h_val⟩
        have : sol₂ (matrixIndex vertices colors v c) ≤ 0 :=
          Int.le_iff_lt_add_one.mpr this
        exact Int.le_antisymm this h_lb

    have h₂'_zero : sol₂' (matrixIndex vertices colors v c) = 0 := by
      have h_bound_mem : bound (matrixIndex vertices colors v c) 0 1 ∈
          (graph_coloring_matrix vertices colors edges).constraints := by
        unfold graph_coloring_matrix
        simp [matrix_bounds_2, List.finRange]
      have h_bound_sat := h_sol₂' (bound (matrixIndex vertices colors v c) 0 1) h_bound_mem
      unfold IntCSP.satisfiesConstraintInt at h_bound_sat
      unfold bound at h_bound_sat
      unfold CSP.satisfies_dynamic_constraint CSP.satisfies_constraint at h_bound_sat
      unfold CSP.map_assignment at h_bound_sat
      simp [CSP.sat, extractValues, _root_.Vector.get] at h_bound_sat
      by_cases h_val : sol₂' (matrixIndex vertices colors v c) = 1
      · have : c = c₂' := h₂'_uniq c h_val
        have : c = c₂ := calc c = c₂' := this
                              _ = c₂ := h_c_eq.symm
        exact absurd this h_case
      · have h_lb := h_bound_sat.1
        have h_ub := h_bound_sat.2
        have : sol₂' (matrixIndex vertices colors v c) < 1 :=
          Int.lt_iff_le_and_ne.mpr ⟨h_ub, h_val⟩
        have : sol₂' (matrixIndex vertices colors v c) ≤ 0 :=
          Int.le_iff_lt_add_one.mpr this
        exact Int.le_antisymm this h_lb

    rw [h₂_zero, h₂'_zero]

end MainTheorems

-- ============================================================================
-- π-Equivalence Theorem
-- ============================================================================

theorem graph_coloring_pi_equivalent (vertices colors : ℕ) (h_colors : 0 < colors)
    (edges : List (Fin vertices × Fin vertices)) :
    piEquivalent
      (graph_coloring_vertex vertices colors edges)
      (graph_coloring_matrix vertices colors edges)
      (@π vertices colors) := by
  have h_forward : ∀ sol₂, IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂ →
      IntCSP.isSolutionInt (graph_coloring_vertex vertices colors edges) (π sol₂) :=
    forward edges
  have h_backward : ∀ sol₁, IntCSP.isSolutionInt (graph_coloring_vertex vertices colors edges) sol₁ →
      ∃ sol₂, IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂ ∧ π sol₂ = sol₁ :=
    backward edges h_colors
  have h_injective : ∀ sol₂ sol₂', IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂ →
      IntCSP.isSolutionInt (graph_coloring_matrix vertices colors edges) sol₂' →
      π sol₂ = π sol₂' → sol₂ = sol₂' :=
    injective edges h_colors
  constructor
  · exact h_forward
  constructor
  · exact h_backward
  · exact h_injective

/-- Derived: Full equivalence -/
theorem graph_coloring_equivalent (vertices colors : ℕ) (h_colors : 0 < colors)
    (edges : List (Fin vertices × Fin vertices)) :
    equivalent
      (graph_coloring_matrix vertices colors edges)
      (graph_coloring_vertex vertices colors edges) := by
  apply piEquivalent_implies_equivalent
  exact graph_coloring_pi_equivalent vertices colors h_colors edges

/-- Derived: Equisatisfiability -/
theorem graph_coloring_equisatisfiable (vertices colors : ℕ) (h_colors : 0 < colors)
    (edges : List (Fin vertices × Fin vertices)) :
    equisatisfiable
      (graph_coloring_vertex vertices colors edges)
      (graph_coloring_matrix vertices colors edges) := by
  apply piEquivalent_implies_equisatisfiable
  exact graph_coloring_pi_equivalent vertices colors h_colors edges

-- ============================================================================
-- Solver Translation
-- ============================================================================

def petersenEdges : List (Fin 10 × Fin 10) :=
  [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9)
  ]

def main : IO Unit := do
  let colors := [2, 3, 4, 5, 6, 7, 8, 9, 10]

  IO.println "Generating instances for coloring the Petersen Graph..."

  for k in colors do
    IO.println s!"Generating instance for {k} colors..."

    let csp_vertex := graph_coloring_vertex 10 k petersenEdges
    let csp_matrix := graph_coloring_matrix 10 k petersenEdges

    -- Vertex formulation
    saveToAuto csp_vertex s!"CSP/L2S/Proofs/mzn/graphcoloring_eq/vertex_{k}" BackendType.MiniZinc
    saveToAuto csp_vertex s!"CSP/L2S/Proofs/smt2/graphcoloring_eq/vertex_{k}" BackendType.SMTLIB

    -- Matrix formulation
    saveToAuto csp_matrix s!"CSP/L2S/Proofs/mzn/graphcoloring_eq/matrix_{k}" BackendType.MiniZinc
    saveToAuto csp_matrix s!"CSP/L2S/Proofs/smt2/graphcoloring_eq/matrix_{k}" BackendType.SMTLIB

  IO.println "All instances generated"
