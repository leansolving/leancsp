import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# 0-1 Knapsack Problem
CSPLib Problem 133

## Problem Description
Given items with weights and values, select a subset that fits in a knapsack
of limited capacity while staying within the weight limit and achieving a
target value threshold.

This is a satisfaction version of the classic optimization problem:
Can we achieve a certain value while respecting the capacity constraint?

## CSP Formulation
- **Variables**: n binary variables (take item or not)
- **Domain**: 0..1 for all variables
- **Constraints**:
  1. Weight capacity: Σ(weights[i] * take[i]) ≤ capacity
  2. Value target: Σ(values[i] * take[i]) ≥ target

## Mathematical Form
Two weighted sum constraints with relational operators:
- Weight: w₀*x₀ + w₁*x₁ + ... + wₙ₋₁*xₙ₋₁ ≤ capacity
- Value:  v₀*x₀ + v₁*x₁ + ... + vₙ₋₁*xₙ₋₁ ≥ target

## Source
CSPLib Problem 133, classic combinatorial optimization problem
-/

-- Helper to create variable scope for all n variables
def allVarsN (n : ℕ) : _root_.Vector (HomogeneousVarIndex n) n :=
  _root_.Vector.ofFn id

-- Helper to create coefficient vector from list
def makeCoeffVector (n : ℕ) (coeffs : List ℤ) (h : coeffs.length = n) :
    _root_.Vector ℤ n :=
  ⟨coeffs.toArray, by simp [h]⟩

-- Parametrized 0-1 knapsack CSP
def knapsack_csp (n : ℕ) (weights values : List ℤ)
    (capacity target : ℤ)
    (h_weights : weights.length = n)
    (h_values : values.length = n) : HomogeneousCSP :=
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
def knapsack_10_50_80 : HomogeneousCSP :=
  let weights := [10, 20, 30, 15, 25, 12, 8, 18, 22, 16]
  let values  := [20, 30, 45, 25, 40, 22, 15, 35, 42, 28]
  knapsack_csp 10 weights values 50 80 rfl rfl

def main : IO Unit := do
  saveAllBackendsAutoTimed knapsack_10_50_80
