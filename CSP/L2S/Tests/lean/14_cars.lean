import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Car Sequencing (CSPLib #001)

Schedule cars with capacity constraints: at most m cars with option o in any b consecutive slots.
-/

structure CarSeqData where
  n_cars : ℕ
  n_options : ℕ
  n_classes : ℕ
  option_max_per_block : List ℕ
  option_block_size : List ℕ
  cars_in_class : List ℕ
  class_option_need : List (List ℕ)

def class_var_idx (i : ℕ) : ℕ := i

def option_var_idx (data : CarSeqData) (p : ℕ) (i : ℕ) : ℕ :=
  data.n_cars + p * data.n_cars + i

def class_var_indices (data : CarSeqData) : List ℕ :=
  List.range data.n_cars

def option_indices (data : CarSeqData) (p : ℕ) : List ℕ :=
  List.range data.n_cars |>.map (option_var_idx data p)

def generate_bounds (data : CarSeqData) : List (IntConstraint (data.n_cars + data.n_cars * data.n_options)) :=
  let class_bounds := (List.finRange data.n_cars).map fun ⟨i, h⟩ =>
    bound ⟨i, by omega⟩ 1 data.n_classes
  let option_bounds := (List.finRange data.n_options).flatMap fun ⟨p, hp⟩ =>
    (List.finRange data.n_cars).map fun ⟨i, hi⟩ =>
      let var_idx := option_var_idx data p i
      bound ⟨var_idx, by
        show var_idx < data.n_cars + data.n_cars * data.n_options
        show data.n_cars + p * data.n_cars + i < data.n_cars + data.n_cars * data.n_options
        have h_p_le : p + 1 ≤ data.n_options := Nat.succ_le_of_lt hp
        calc data.n_cars + p * data.n_cars + i
          < data.n_cars + p * data.n_cars + data.n_cars := by omega
          _ = data.n_cars + (p + 1) * data.n_cars := by ring
          _ ≤ data.n_cars + data.n_options * data.n_cars := by
              have : (p + 1) * data.n_cars ≤ data.n_options * data.n_cars := Nat.mul_le_mul_right data.n_cars h_p_le
              omega
          _ = data.n_cars + data.n_cars * data.n_options := by ring
      ⟩ 0 1
  class_bounds ++ option_bounds

def nat_list_to_fin_vector {num_vars : ℕ} (indices : List ℕ)
    (h : ∀ i ∈ indices, i < num_vars) : _root_.Vector (Fin num_vars) indices.length :=
  ⟨(indices.attach.map fun ⟨i, hi⟩ => ⟨i, h i hi⟩).toArray, by simp [List.length_attach]⟩

def generate_count_constraints (data : CarSeqData) :
    List (IntConstraint (data.n_cars + data.n_cars * data.n_options)) :=
  let class_indices := class_var_indices data
  let class_vars := nat_list_to_fin_vector class_indices (by
    intro i hi
    show i < data.n_cars + data.n_cars * data.n_options
    have : i ∈ List.range data.n_cars := hi
    have : i < data.n_cars := List.mem_range.mp this
    omega
  )
  (List.finRange data.n_classes).filterMap fun ⟨c, hc⟩ =>
    match data.cars_in_class[c]? with
    | some demand => some (count class_vars (c + 1) demand)
    | none => none

def generate_sliding_constraints (data : CarSeqData) :
    List (IntConstraint (data.n_cars + data.n_cars * data.n_options)) :=
  (List.finRange data.n_options).filterMap fun ⟨p, hp⟩ =>
    match data.option_block_size[p]?, data.option_max_per_block[p]? with
    | some block_size, some max_count =>
        let opt_indices := option_indices data p
        let opt_vars := nat_list_to_fin_vector opt_indices (by
          intro i hi
          show i < data.n_cars + data.n_cars * data.n_options
          have h_in_range : i ∈ (List.range data.n_cars).map (option_var_idx data p) := hi
          obtain ⟨j, hj_mem, hj_eq⟩ := List.mem_map.mp h_in_range
          have hj_lt : j < data.n_cars := List.mem_range.mp hj_mem
          rw [← hj_eq]
          show data.n_cars + p * data.n_cars + j < data.n_cars + data.n_cars * data.n_options
          have h_p_le : p + 1 ≤ data.n_options := Nat.succ_le_of_lt hp
          calc data.n_cars + p * data.n_cars + j
            < data.n_cars + p * data.n_cars + data.n_cars := by omega
            _ = data.n_cars + (p + 1) * data.n_cars := by ring
            _ ≤ data.n_cars + data.n_options * data.n_cars := by
                have : (p + 1) * data.n_cars ≤ data.n_options * data.n_cars := Nat.mul_le_mul_right data.n_cars h_p_le
                omega
            _ = data.n_cars + data.n_cars * data.n_options := by ring
        )
        some (sliding_sum_le opt_vars block_size max_count)
    | _, _ => none

def car_sequencing_csp (data : CarSeqData) : IntCSP :=
  let num_vars := data.n_cars + data.n_cars * data.n_options
  ⟨num_vars,
   generate_bounds data ++
   generate_count_constraints data ++
   generate_sliding_constraints data⟩

def cars1_data : CarSeqData := {
  n_cars := 10
  n_options := 5
  n_classes := 6
  option_max_per_block := [1, 2, 1, 2, 1]
  option_block_size := [2, 3, 3, 5, 5]
  cars_in_class := [1, 1, 2, 2, 2, 2]
  class_option_need := [
    [1, 0, 1, 1, 0],
    [0, 0, 0, 1, 0],
    [0, 1, 0, 0, 1],
    [0, 1, 0, 1, 0],
    [1, 0, 1, 0, 0],
    [1, 1, 0, 0, 0]
  ]
}

def cars_csp := car_sequencing_csp cars1_data

def main : IO Unit := do
  saveAllBackendsAutoTimed cars_csp
