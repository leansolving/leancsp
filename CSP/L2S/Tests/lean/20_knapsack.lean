import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# 0-1 knapsack (satisfaction form)

Given item weights and values, choose a subset — one binary variable per item —
with `Σ weightᵢ·xᵢ ≤ capacity` and `Σ valueᵢ·xᵢ ≥ target`.  Two weighted-sum
constraints.  CSPLib problem 133.
-/

-- Helper to create variable scope for all n variables
def allVarsN (n : ℕ) : _root_.Vector (VarType n) n :=
  _root_.Vector.ofFn id

-- Helper to create coefficient vector from list
def makeCoeffVector (n : ℕ) (coeffs : List ℤ) (h : coeffs.length = n) :
    _root_.Vector ℤ n :=
  ⟨coeffs.toArray, by simp [h]⟩

-- Parametrized 0-1 knapsack CSP
def knapsack_csp (n : ℕ) (weights values : List ℤ)
    (capacity target : ℤ)
    (h_weights : weights.length = n)
    (h_values : values.length = n) : IntCSP :=
  let bounds_list := (List.finRange n).map fun i => bound i 0 1
  let weight_coeffs := makeCoeffVector n weights h_weights
  let value_coeffs := makeCoeffVector n values h_values
  let weight_constraint := linear_le (allVarsN n) weight_coeffs capacity
  let value_constraint := linear_ge (allVarsN n) value_coeffs target
  ⟨n, bounds_list ++ [weight_constraint, value_constraint]⟩

-- Specific instance
-- n = 10 items
-- weights = [10, 20, 30, 15, 25, 12, 8, 18, 22, 16]
-- values  = [20, 30, 45, 25, 40, 22, 15, 35, 42, 28]
-- capacity = 50
-- target_value = 80
def knapsack_10_50_80 : IntCSP :=
  let weights := [10, 20, 30, 15, 25, 12, 8, 18, 22, 16]
  let values  := [20, 30, 45, 25, 40, 22, 15, 35, 42, 28]
  knapsack_csp 10 weights values 50 80 rfl rfl
