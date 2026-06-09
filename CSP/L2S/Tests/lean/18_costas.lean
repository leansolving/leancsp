import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Costas Array Problem
CSPLib Problem 076

## Problem Description
A Costas array is a permutation of 1..n such that all pairwise differences
(both horizontal and vertical) are distinct. Used in sonar and radar for
minimal cross-correlation.

## CSP Formulation
- **Primary variables**: n array positions, domain [1, n]
- **Auxiliary variables**: n(n-1)/2 difference variables organized by offset
  - For offset k=1: (n-1) differences
  - For offset k=2: (n-2) differences
  - ...
  - For offset k=n-1: 1 difference
- **Total variables**: n + n(n-1)/2
- **Variable mapping**:
  - Costas array: indices 0..(n-1)
  - Differences: indices n onward, grouped by offset

## Constraints
1. Bounds: costas[i] ∈ [1, n], diff[k] ∈ [-(n-1), n-1]
2. Alldifferent on costas (permutation)
3. For each offset k: alldifferent on differences at that offset
4. Difference definition: diff[offset,i] = costas[i+offset] - costas[i]

## Parametrized Design
- `costas_csp(n, num_vars)` - general formulation for array size n
- `costas_8` - standard n=8 instance

## Source
CSPLib Problem 076
-/

-- Helper: compute number of differences for all offsets
-- Total = (n-1) + (n-2) + ... + 1 = n(n-1)/2
def total_diffs (n : ℕ) : ℕ := n * (n - 1) / 2

-- Helper: compute starting index for differences at offset k
-- Offset 1 starts at n, offset 2 starts at n+(n-1), etc.
def diff_start_index (n k : ℕ) : ℕ :=
  n + (k - 1) * n - (k - 1) * k / 2

-- Parametrized Costas Array CSP
def costas_csp (n num_vars : ℕ) : IntCSP :=
  -- Bounds for costas array (indices 0..n-1): domain [1, n]
  let costas_bounds := (List.range n).filterMap fun i =>
    if h : i < num_vars then
      some (bound ⟨i, h⟩ 1 n)
    else
      none

  -- Bounds for all difference variables: domain [-(n-1), n-1]
  let diff_start := n
  let num_diffs := total_diffs n
  let diff_bounds := (List.range num_diffs).filterMap fun k =>
    let d_idx := diff_start + k
    if h : d_idx < num_vars then
      some (bound ⟨d_idx, h⟩ (-(n - 1 : ℤ)) (n - 1))
    else
      none

  -- Alldifferent on costas array
  let costas_var_list := (List.range n).filterMap fun i =>
    if h : i < num_vars then
      some ⟨i, h⟩
    else
      none
  let costas_alldiff_opt :=
    if h_len : costas_var_list.length = n then
      let costas_vars : _root_.Vector (VarType num_vars) n :=
        ⟨costas_var_list.toArray, by simp; exact h_len⟩
      some (alldifferent costas_vars)
    else
      none
  let costas_alldiff_list := match costas_alldiff_opt with
    | some c => [c]
    | none => []

  -- For each offset k, create difference constraints and alldifferent
  let offset_constraints := (List.range (n - 1)).flatMap fun k_idx =>
    let offset := k_idx + 1  -- offset ranges from 1 to n-1
    let num_pairs := n - offset  -- number of pairs at this offset

    -- Create difference constraints: diff = costas[i+offset] - costas[i]
    let diff_defs := (List.range num_pairs).filterMap fun i =>
      let costas_i := i
      let costas_j := i + offset
      let diff_idx := diff_start_index n offset + i
      if hi : costas_i < num_vars then
        if hj : costas_j < num_vars then
          if hd : diff_idx < num_vars then
            -- diff = costas[j] - costas[i]
            let scope : _root_.Vector (VarType num_vars) 3 :=
              ⟨#[⟨costas_j, hj⟩, ⟨costas_i, hi⟩, ⟨diff_idx, hd⟩], rfl⟩
            let coeffs : _root_.Vector ℤ 3 := ⟨#[1, -1, -1], rfl⟩
            some (linear_eq scope coeffs 0)
          else
            none
        else
          none
      else
        none

    -- Alldifferent on differences at this offset
    let diff_var_list := (List.range num_pairs).filterMap fun i =>
      let diff_idx := diff_start_index n offset + i
      if h : diff_idx < num_vars then
        some ⟨diff_idx, h⟩
      else
        none
    let alldiff_opt :=
      if h_len : diff_var_list.length = num_pairs then
        let diff_vars : _root_.Vector (VarType num_vars) num_pairs :=
          ⟨diff_var_list.toArray, by simp; exact h_len⟩
        some (alldifferent diff_vars)
      else
        none
    let alldiff_list := match alldiff_opt with
      | some c => [c]
      | none => []

    diff_defs ++ alldiff_list

  ⟨num_vars, costas_bounds ++ diff_bounds ++ costas_alldiff_list ++ offset_constraints⟩

-- Standard n=8 Costas Array instance
-- n = 8, num_diffs = 8*7/2 = 28, num_vars = 8 + 28 = 36
def costas_8 : IntCSP :=
  costas_csp 8 36

def main : IO Unit := do
  saveAllBackendsAutoTimed costas_8
