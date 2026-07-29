import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Propagation stress test

`N` variables `y[0]..y[N-1]` over `0..N`, subject to the non-decreasing chain
`y[i-1] ≤ y[i]` and the extra inequalities `y[0] ≤ y[i] + C`.  All constraints are
linear, so this stresses propagation rather than search.
-/

-- Helper to create chain inequality: y[i-1] - y[i] <= 0
def make_chain_constraint (n : ℕ) (i : ℕ) (h1 : i > 0) (h2 : i < n) :
    IntConstraint n :=
  let scope : _root_.Vector (VarType n) 2 :=
    ⟨#[⟨i - 1, by omega⟩, ⟨i, h2⟩], rfl⟩
  let coeffs : _root_.Vector ℤ 2 := ⟨#[1, -1], rfl⟩
  linear_le scope coeffs 0

-- Helper to create constraint from y[0]: y[0] - y[i] <= C
def make_y0_constraint (n : ℕ) (c : ℤ) (i : ℕ) (h1 : i > 0) (h2 : i < n) :
    IntConstraint n :=
  let scope : _root_.Vector (VarType n) 2 :=
    ⟨#[⟨0, by omega⟩, ⟨i, h2⟩], rfl⟩
  let coeffs : _root_.Vector ℤ 2 := ⟨#[1, -1], rfl⟩
  linear_le scope coeffs c

-- Parametrized propagation stress test CSP
def prop_stress_csp (n : ℕ) (c : ℤ) : IntCSP :=
  let bounds_list := (List.finRange n).map fun i => bound i 0 (n : ℤ)
  -- Chain constraints: y[i-1] - y[i] <= 0 for i in 1..n-1
  let chain_constraints := (List.range (n - 1)).filterMap fun k =>
    let i := k + 1
    if h1 : i > 0 then
      if h2 : i < n then
        some (make_chain_constraint n i h1 h2)
      else none
    else none
  -- Constraints from y[0]: y[0] - y[i] <= C for i in 1..n-1
  let y0_constraints := (List.range (n - 1)).filterMap fun k =>
    let i := k + 1
    if h1 : i > 0 then
      if h2 : i < n then
        some (make_y0_constraint n c i h1 h2)
      else none
    else none
  ⟨n, bounds_list ++ chain_constraints ++ y0_constraints⟩

-- Specific instance: N=100, C=10
def prop_stress_100_10 : IntCSP :=
  prop_stress_csp 100 10
