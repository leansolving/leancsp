import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Latin squares, binary encoding

An `n×n` Latin square encoded with `n³` binary variables `x[i,j,k] ∈ {0,1}`, where
`x[i,j,k] = 1` iff cell `(i,j)` holds value `k`.  Three families of exactly-one
constraints: one value per cell, each value once per row, each value once per column.

At `n = 5` that is 125 variables and 200 constraints — a scalability stress test.
-/

-- Helper: Compute linear index for 3D position (i,j,k) in flattened array
def latin_idx (n : ℕ) (i j k : ℕ) : ℕ := i * n * n + j * n + k

-- Helper: Indices for all values k at cell (i,j)
def cell_value_indices (n : ℕ) (i j : ℕ) : List ℕ :=
  List.range n |>.map (latin_idx n i j)

-- Helper: Indices for value k across row i
def row_value_indices (n : ℕ) (i k : ℕ) : List ℕ :=
  List.range n |>.map fun j => latin_idx n i j k

-- Helper: Indices for value k down column j
def col_value_indices (n : ℕ) (j k : ℕ) : List ℕ :=
  List.range n |>.map fun i => latin_idx n i j k

-- Convert list of indices to Vector of Fin
def indices_to_vector (num_vars : ℕ) (indices : List ℕ)
    (h : ∀ i ∈ indices, i < num_vars) : _root_.Vector (Fin num_vars) indices.length :=
  ⟨(indices.attach.map fun ⟨i, hi⟩ => ⟨i, h i hi⟩).toArray, by simp [List.length_attach]⟩

-- General Latin square CSP with binary encoding - parametrized for any size
def latin_square_csp (n : ℕ) : IntCSP :=
  let num_vars := n * n * n

  -- All variables are binary
  let bounds := (List.finRange num_vars).map fun i => bound i 0 1

  -- Cell constraints: each cell has exactly one value
  let cell_constraints := (List.finRange n).flatMap fun ⟨i, h_i⟩ =>
    (List.finRange n).map fun ⟨j, h_j⟩ =>
      let indices := cell_value_indices n i j
      sum_eq (indices_to_vector num_vars indices (by
        intro idx h_in
        show idx < num_vars
        -- h_in : idx ∈ indices, and indices = cell_value_indices n i j
        -- cell_value_indices n i j = (List.range n).map (latin_idx n i j)
        have : idx ∈ (List.range n).map (latin_idx n i j) := h_in
        obtain ⟨k, h_k_mem, h_eq⟩ := List.mem_map.mp this
        have h_k' : k < n := List.mem_range.mp h_k_mem
        rw [← h_eq]
        unfold latin_idx num_vars
        -- idx = i*n*n + j*n + k, need idx < n*n*n with i < n, j < n, k < n
        have : i * n * n + j * n + k < n * n * n := by
          calc i * n * n + j * n + k
            < i * n * n + j * n + n := by omega
            _ = i * n * n + (j + 1) * n := by ring
            _ ≤ i * n * n + n * n := by
              have h1 : j + 1 ≤ n := Nat.succ_le_of_lt h_j
              have h2 : (j + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
              omega
            _ = (i + 1) * n * n := by ring
            _ ≤ n * n * n := by
              have h1 : i + 1 ≤ n := Nat.succ_le_of_lt h_i
              have h2 : (i + 1) * n * n ≤ n * n * n := by
                have h3 : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
                have h4 : (i + 1) * n * n ≤ n * n * n := Nat.mul_le_mul_right n h3
                exact h4
              exact h2
        exact this
      )) 1

  -- Row constraints: each value appears once per row
  let row_constraints := (List.finRange n).flatMap fun ⟨i, h_i⟩ =>
    (List.finRange n).map fun ⟨k, h_k⟩ =>
      let indices := row_value_indices n i k
      sum_eq (indices_to_vector num_vars indices (by
        intro idx h_in
        show idx < num_vars
        -- h_in : idx ∈ indices, and indices = row_value_indices n i k
        -- row_value_indices n i k = (List.range n).map (fun j => latin_idx n i j k)
        have : idx ∈ (List.range n).map (fun j => latin_idx n i j k) := h_in
        obtain ⟨j, h_j_mem, h_eq⟩ := List.mem_map.mp this
        have h_j' : j < n := List.mem_range.mp h_j_mem
        rw [← h_eq]
        unfold latin_idx num_vars
        -- idx = i*n*n + j*n + k, need idx < n*n*n with i < n, j < n, k < n
        have : i * n * n + j * n + k < n * n * n := by
          calc i * n * n + j * n + k
            < i * n * n + j * n + n := by omega
            _ = i * n * n + (j + 1) * n := by ring
            _ ≤ i * n * n + n * n := by
              have h1 : j + 1 ≤ n := Nat.succ_le_of_lt h_j'
              have h2 : (j + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
              omega
            _ = (i + 1) * n * n := by ring
            _ ≤ n * n * n := by
              have h1 : i + 1 ≤ n := Nat.succ_le_of_lt h_i
              have h2 : (i + 1) * n * n ≤ n * n * n := by
                have h3 : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
                have h4 : (i + 1) * n * n ≤ n * n * n := Nat.mul_le_mul_right n h3
                exact h4
              exact h2
        exact this
      )) 1

  -- Column constraints: each value appears once per column
  let col_constraints := (List.finRange n).flatMap fun ⟨j, h_j⟩ =>
    (List.finRange n).map fun ⟨k, h_k⟩ =>
      let indices := col_value_indices n j k
      sum_eq (indices_to_vector num_vars indices (by
        intro idx h_in
        show idx < num_vars
        -- h_in : idx ∈ indices, and indices = col_value_indices n j k
        -- col_value_indices n j k = (List.range n).map (fun i => latin_idx n i j k)
        have : idx ∈ (List.range n).map (fun i => latin_idx n i j k) := h_in
        obtain ⟨i, h_i_mem, h_eq⟩ := List.mem_map.mp this
        have h_i' : i < n := List.mem_range.mp h_i_mem
        rw [← h_eq]
        unfold latin_idx num_vars
        -- idx = i*n*n + j*n + k, need idx < n*n*n with i < n, j < n, k < n
        have : i * n * n + j * n + k < n * n * n := by
          calc i * n * n + j * n + k
            < i * n * n + j * n + n := by omega
            _ = i * n * n + (j + 1) * n := by ring
            _ ≤ i * n * n + n * n := by
              have h1 : j + 1 ≤ n := Nat.succ_le_of_lt h_j
              have h2 : (j + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
              omega
            _ = (i + 1) * n * n := by ring
            _ ≤ n * n * n := by
              have h1 : i + 1 ≤ n := Nat.succ_le_of_lt h_i'
              have h2 : (i + 1) * n * n ≤ n * n * n := by
                have h3 : (i + 1) * n ≤ n * n := Nat.mul_le_mul_right n h1
                have h4 : (i + 1) * n * n ≤ n * n * n := Nat.mul_le_mul_right n h3
                exact h4
              exact h2
        exact this
      )) 1

  ⟨num_vars, bounds ++ cell_constraints ++ row_constraints ++ col_constraints⟩

-- Specific instance
def latin_square_inst : IntCSP :=
  latin_square_csp 8
