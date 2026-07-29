import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Rods puzzle

Pick 5 digit positions `M1..M5` in `1..9`, all different, whose rod values
`rods[Mi] = Vi` (with `rods = [1,2,3,4,5,2,3,4,5]`) sum to 12, while the
cryptarithmetic equation `10·M1 + 1000·M2 + M3 − 1000·M4 − 10·M5 = −2982` holds.

MiniZinc expands `rods[M1]` into an element constraint automatically; here the
auxiliary variables `V1..V5` model it explicitly.  10 variables in total.
-/

-- The rods array (1-based indexing in MiniZinc corresponds to 0-based list in Lean)
def rods_array : List ℤ := [1, 2, 3, 4, 5, 2, 3, 4, 5]

-- Helper to create bound constraints for all 10 variables
def rods_bounds : List (IntConstraint 10) :=
  -- Bounds for index variables (M1..M5): domain 1..9
  [ bound 0 1 9, bound 1 1 9, bound 2 1 9, bound 3 1 9, bound 4 1 9,
    -- Bounds for result variables (V1..V5): domain 1..5
    bound 5 1 5, bound 6 1 5, bound 7 1 5, bound 8 1 5, bound 9 1 5 ]

-- Element constraints: rods[Mi] = Vi for i=0..4
-- Mi is variable i, Vi is variable (i+5)
def rods_element_constraints : List (IntConstraint 10) :=
  [ element ⟨0, by omega⟩ ⟨5, by omega⟩ rods_array,
    element ⟨1, by omega⟩ ⟨6, by omega⟩ rods_array,
    element ⟨2, by omega⟩ ⟨7, by omega⟩ rods_array,
    element ⟨3, by omega⟩ ⟨8, by omega⟩ rods_array,
    element ⟨4, by omega⟩ ⟨9, by omega⟩ rods_array ]

-- Sum constraint: V1 + V2 + V3 + V4 + V5 = 12
-- Vi are variables 5, 6, 7, 8, 9
def rods_sum_constraint : IntConstraint 10 :=
  let result_vars : _root_.Vector (VarType 10) 5 :=
    ⟨#[⟨5, by omega⟩, ⟨6, by omega⟩, ⟨7, by omega⟩, ⟨8, by omega⟩, ⟨9, by omega⟩], rfl⟩
  sum_eq result_vars 12

-- Linear equation: 10*M1 + 1000*M2 + 1*M3 - 1000*M4 - 10*M5 = -2982
-- Mi are variables 0, 1, 2, 3, 4
def rods_linear_constraint : IntConstraint 10 :=
  let index_vars : _root_.Vector (VarType 10) 5 :=
    ⟨#[⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩], rfl⟩
  let coeffs : _root_.Vector ℤ 5 := ⟨#[10, 1000, 1, -1000, -10], rfl⟩
  linear_eq index_vars coeffs (-2982)

-- Alldifferent constraint on M1..M5 (variables 0..4)
def rods_alldifferent_constraint : IntConstraint 10 :=
  let index_vars : _root_.Vector (VarType 10) 5 :=
    ⟨#[⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩], rfl⟩
  alldifferent index_vars

-- Complete CSP
def rods_problem : IntCSP :=
  ⟨10,
   rods_bounds ++
   rods_element_constraints ++
   [rods_sum_constraint, rods_linear_constraint, rods_alldifferent_constraint]⟩
