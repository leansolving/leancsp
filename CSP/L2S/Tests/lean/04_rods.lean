import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Rods Puzzle (04_rods)

This puzzle involves finding 5 digit positions (1..9) such that:
1. The sum of rods at those positions equals 12
2. A cryptarithmetic equation holds
3. All positions are different

## Problem Details
- **Variables**: 10 variables total
  - M1..M5 (indices 0-4): Position variables with domain 1..9
  - V1..V5 (indices 5-9): Result variables with domain 1..5 (values in rods array)
- **Array**: rods[1..9] = [1,2,3,4,5,2,3,4,5]
- **Constraints**:
  1. Element: rods[Mi] = Vi for i=1..5
  2. Sum: V1 + V2 + V3 + V4 + V5 = 12
  3. Linear equation: 2303 + M1*10 + 980 + M2*1000 + M3 = 301 + M4*1000 + M5*10
     Simplified: 10*M1 + 1000*M2 + 1*M3 - 1000*M4 - 10*M5 = -2982
  4. Alldifferent: M1, M2, M3, M4, M5 all different

## MiniZinc Translation Note
In MiniZinc, `rods[M1]` is automatically expanded to an element constraint.
In L2M, we must explicitly model this using auxiliary variables V1..V5.
-/

-- The rods array (1-based indexing in MiniZinc corresponds to 0-based list in Lean)
def rods_array : List ℤ := [1, 2, 3, 4, 5, 2, 3, 4, 5]

-- Helper to create bound constraints for all 10 variables
def rods_bounds : List (TaggedConstraint 10) :=
  -- Bounds for index variables (M1..M5): domain 1..9
  [ bound 0 1 9, bound 1 1 9, bound 2 1 9, bound 3 1 9, bound 4 1 9,
    -- Bounds for result variables (V1..V5): domain 1..5
    bound 5 1 5, bound 6 1 5, bound 7 1 5, bound 8 1 5, bound 9 1 5 ]

-- Element constraints: rods[Mi] = Vi for i=0..4
-- Mi is variable i, Vi is variable (i+5)
def rods_element_constraints : List (TaggedConstraint 10) :=
  [ element ⟨0, by omega⟩ ⟨5, by omega⟩ rods_array,
    element ⟨1, by omega⟩ ⟨6, by omega⟩ rods_array,
    element ⟨2, by omega⟩ ⟨7, by omega⟩ rods_array,
    element ⟨3, by omega⟩ ⟨8, by omega⟩ rods_array,
    element ⟨4, by omega⟩ ⟨9, by omega⟩ rods_array ]

-- Sum constraint: V1 + V2 + V3 + V4 + V5 = 12
-- Vi are variables 5, 6, 7, 8, 9
def rods_sum_constraint : TaggedConstraint 10 :=
  let result_vars : _root_.Vector (VarType 10) 5 :=
    ⟨#[⟨5, by omega⟩, ⟨6, by omega⟩, ⟨7, by omega⟩, ⟨8, by omega⟩, ⟨9, by omega⟩], rfl⟩
  sum_eq result_vars 12

-- Linear equation: 10*M1 + 1000*M2 + 1*M3 - 1000*M4 - 10*M5 = -2982
-- Mi are variables 0, 1, 2, 3, 4
def rods_linear_constraint : TaggedConstraint 10 :=
  let index_vars : _root_.Vector (VarType 10) 5 :=
    ⟨#[⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩], rfl⟩
  let coeffs : _root_.Vector ℤ 5 := ⟨#[10, 1000, 1, -1000, -10], rfl⟩
  linear_eq index_vars coeffs (-2982)

-- Alldifferent constraint on M1..M5 (variables 0..4)
def rods_alldifferent_constraint : TaggedConstraint 10 :=
  let index_vars : _root_.Vector (VarType 10) 5 :=
    ⟨#[⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩], rfl⟩
  alldifferent index_vars

-- Complete CSP
def rods_problem : IntCSP :=
  ⟨10,
   rods_bounds ++
   rods_element_constraints ++
   [rods_sum_constraint, rods_linear_constraint, rods_alldifferent_constraint]⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed rods_problem
