import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# All-interval series

Find a permutation of `0..n-1` whose consecutive absolute differences form a
permutation of `1..n-1`; e.g. `[0,3,1,2]` has differences `[3,2,1]`.

`2n-1` variables: the `n` series positions (indices `0..n-1`, domain `[0,n-1]`) and
`n-1` difference variables (indices `n..2n-2`, domain `[1,n-1]`), linked by
`abs_diff_var`.  Both groups are `alldifferent`, with `x[0] < x[n-1]` and
`diff[0] < diff[1]` breaking symmetry.  CSPLib problem 007.
-/

-- Parametrized All-Interval Series CSP
-- num_vars = 2n - 1 (n series + n-1 differences)
def all_interval_csp (n num_vars : ℕ) : IntCSP :=
  -- Bounds for series variables (indices 0..n-1): domain [0, n-1]
  let series_bounds := (List.range n).filterMap fun i =>
    if h : i < num_vars then
      some (bound ⟨i, h⟩ 0 (n - 1))
    else
      none

  -- Bounds for difference variables (indices n..2n-2): domain [1, n-1]
  let diff_bounds := (List.range (n - 1)).filterMap fun k =>
    let d_idx := n + k
    if h : d_idx < num_vars then
      some (bound ⟨d_idx, h⟩ 1 (n - 1))
    else
      none

  -- Alldifferent on series variables (indices 0..n-1)
  let series_var_list := (List.range n).filterMap fun i =>
    if h : i < num_vars then
      some ⟨i, h⟩
    else
      none
  let series_alldiff_opt :=
    if h_len : series_var_list.length = n then
      let series_vars : _root_.Vector (VarType num_vars) n :=
        ⟨series_var_list.toArray, by simp; exact h_len⟩
      some (alldifferent series_vars)
    else
      none
  let series_alldiff_list := match series_alldiff_opt with
    | some c => [c]
    | none => []

  -- Alldifferent on difference variables (indices n..2n-2)
  let diff_var_list := (List.range (n - 1)).filterMap fun k =>
    let d_idx := n + k
    if h : d_idx < num_vars then
      some ⟨d_idx, h⟩
    else
      none
  let diff_alldiff_opt :=
    if h_len : diff_var_list.length = n - 1 then
      let diff_vars : _root_.Vector (VarType num_vars) (n - 1) :=
        ⟨diff_var_list.toArray, by simp; exact h_len⟩
      some (alldifferent diff_vars)
    else
      none
  let diff_alldiff_list := match diff_alldiff_opt with
    | some c => [c]
    | none => []

  -- Difference definitions: diff[k] = abs(x[k+1] - x[k])
  -- Use abs_diff_var: result = |var1 - var2|
  let diff_defs := (List.range (n - 1)).filterMap fun k =>
    let i := k        -- series index
    let j := k + 1    -- next series index
    let d_idx := n + k  -- difference variable index
    if hi : i < num_vars then
      if hj : j < num_vars then
        if hd : d_idx < num_vars then
          some (abs_diff_var ⟨i, hi⟩ ⟨j, hj⟩ ⟨d_idx, hd⟩)
        else
          none
      else
        none
    else
      none

  -- Symmetry breaking: x[0] < x[n-1]
  let sym_series_opt :=
    if h0 : 0 < num_vars then
      if hn : n - 1 < num_vars then
        some (less_than ⟨0, h0⟩ ⟨n - 1, hn⟩)
      else
        none
    else
      none
  let sym_series_list := match sym_series_opt with
    | some c => [c]
    | none => []

  -- Symmetry breaking: diff[0] < diff[1]
  let sym_diff_opt :=
    if h0 : n < num_vars then
      if h1 : n + 1 < num_vars then
        some (less_than ⟨n, h0⟩ ⟨n + 1, h1⟩)
      else
        none
    else
      none
  let sym_diff_list := match sym_diff_opt with
    | some c => [c]
    | none => []

  ⟨num_vars, series_bounds ++ diff_bounds ++ series_alldiff_list ++
             diff_alldiff_list ++ diff_defs ++ sym_series_list ++ sym_diff_list⟩

-- Standard n=10 All-Interval Series instance
-- n = 10 series elements, n-1 = 9 differences, num_vars = 10 + 9 = 19
def all_interval_10 : IntCSP :=
  all_interval_csp 10 19
