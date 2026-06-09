import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Golomb Ruler (CSPLib #006)

Find m marks on a ruler where all pairwise distances are distinct.
Variables: m marks + m(m-1)/2 differences. Symmetry breaking included.
-/

def all_mark_pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun i =>
    (List.range m).filterMap fun j =>
      if i < j then some (i, j) else none

def make_diff_constraint (num_vars : ℕ) (i j d : ℕ)
    (hi : i < num_vars) (hj : j < num_vars) (hd : d < num_vars) :
    IntConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 3 :=
    ⟨#[⟨j, hj⟩, ⟨i, hi⟩, ⟨d, hd⟩], rfl⟩
  let coeffs : _root_.Vector ℤ 3 := ⟨#[1, -1, -1], rfl⟩
  linear_eq scope coeffs 0

def golomb_csp (m num_vars : ℕ) : IntCSP :=
  let upper_bound := m * m
  let pairs := all_mark_pairs m

  let bounds_list := (List.finRange num_vars).map fun i =>
    if i.val < m then bound i 0 upper_bound else bound i 1 upper_bound

  let first_zero_opt :=
    if h : 0 < num_vars then some (equals_const ⟨0, h⟩ 0) else none
  let first_zero_list := match first_zero_opt with
    | some c => [c]
    | none => []

  let increasing := (List.range (m - 1)).filterMap fun i =>
    if h1 : i < num_vars then
      if h2 : i + 1 < num_vars then some (less_than ⟨i, h1⟩ ⟨i + 1, h2⟩)
      else none
    else none

  let diff_defs := pairs.mapIdx (fun k (i, j) =>
    let d_idx := m + k
    if hi : i < num_vars then
      if hj : j < num_vars then
        if hd : d_idx < num_vars then some (make_diff_constraint num_vars i j d_idx hi hj hd)
        else none
      else none
    else none) |>.filterMap id

  let num_diffs := pairs.length
  let diff_var_list := (List.range num_diffs).filterMap fun k =>
    if h : m + k < num_vars then some ⟨m + k, h⟩ else none
  let diff_vars : _root_.Vector (VarType num_vars) diff_var_list.length :=
    ⟨diff_var_list.toArray, by simp⟩
  let alldiff := alldifferent diff_vars

  let first_diff_idx := m
  let last_diff_idx := m + num_diffs - 1
  let sym_break_opt :=
    if h1 : first_diff_idx < num_vars then
      if h2 : last_diff_idx < num_vars then some (less_than ⟨first_diff_idx, h1⟩ ⟨last_diff_idx, h2⟩)
      else none
    else none
  let sym_break_list := match sym_break_opt with
    | some c => [c]
    | none => []

  ⟨num_vars, bounds_list ++ first_zero_list ++ increasing ++ diff_defs ++ [alldiff] ++ sym_break_list⟩

def golomb_8 : IntCSP :=
  golomb_csp 8 36

def main : IO Unit := do
  saveAllBackendsAutoTimed golomb_8
