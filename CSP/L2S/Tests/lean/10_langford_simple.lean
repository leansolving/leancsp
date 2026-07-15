import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

/-!
# Langford's Problem L(m,n)

Place m copies of each digit 1..n such that for any digit d,
consecutive copies of d are separated by exactly d positions.

## Problem Description
- **Parameters**: n (number of digits), m (copies per digit)
- **Variables**: n×m positions, each with domain 1..n×m
- **Constraint 1**: All positions must be different (alldifferent)
- **Constraint 2**: For digit d and copy c, c+1: x[d,c+1] = x[d,c] + d + 1

## Example L(2,3)
Known solution: [3,1,2,1,3,2]
- Digit 1: positions 2,4 (separated by 1 position) ✓
- Digit 2: positions 3,6 (separated by 2 positions) ✓
- Digit 3: positions 1,5 (separated by 3 positions) ✓

## Mathematical Structure
Variables represent positions where each (digit, copy) pair is placed:
- x[d,c] = position where copy c of digit d is placed
- Flattened to 1D: variable index = (d-1)*m + (c-1)

## Source
CSPLib Problem #024
-/

def langford_var_index (d c m : ℕ) : ℕ := (d - 1) * m + (c - 1)

-- Create bound constraints for all variables (domain 1..n×m)
def langford_bounds (n m : ℕ) : List (IntConstraint (n * m)) :=
  List.finRange (n * m) |>.map (fun i => bound i 1 (n * m))

def make_spacing_constraint (num_vars : ℕ) (var1 var2 : ℕ) (d : ℕ)
    (h1 : var1 < num_vars) (h2 : var2 < num_vars) : IntConstraint num_vars :=
  let scope : _root_.Vector (VarType num_vars) 2 :=
    ⟨#[⟨var2, h2⟩, ⟨var1, h1⟩], rfl⟩
  let coeffs : _root_.Vector ℤ 2 := ⟨#[1, -1], rfl⟩
  linear_eq scope coeffs (d + 1 : ℤ)

-- L(2,3) specific instance - 6 variables
-- Variable mapping: var_index = (digit-1)*2 + (copy-1)
-- Digit 1: vars 0,1;  Digit 2: vars 2,3;  Digit 3: vars 4,5
def langford_2_3_spacing : List (IntConstraint 6) :=
  [ make_spacing_constraint 6 0 1 1 (by decide) (by decide),  -- x[1] - x[0] = 2
    make_spacing_constraint 6 2 3 2 (by decide) (by decide),  -- x[3] - x[2] = 3
    make_spacing_constraint 6 4 5 3 (by decide) (by decide)   -- x[5] - x[4] = 4
  ]

def langford_2_3_alldifferent : IntConstraint 6 :=
  alldifferent (_root_.Vector.ofFn id)

-- L(2,3) complete CSP
def langford_2_3 : IntCSP :=
  ⟨6,
   langford_bounds 3 2 ++
   langford_2_3_spacing ++
   [langford_2_3_alldifferent]⟩

-- General L(2,n): 2n positions, digits 1..n each placed twice.
-- Digit d (1-indexed) uses variables 2(d-1) and 2(d-1)+1; the spacing constraint
-- forces its two copies to be exactly d+1 positions apart, and all positions differ.
-- L(2,n) is solvable iff n ≡ 0 or 3 (mod 4); n = 6 and n = 9 are UNSAT.
def langford_2n_csp (n : ℕ) : IntCSP :=
  let nv := n * 2
  let spacing := (List.range n).filterMap fun d0 =>
    let v1 := d0 * 2
    let v2 := d0 * 2 + 1
    if h1 : v1 < nv then
      if h2 : v2 < nv then
        some (make_spacing_constraint nv v1 v2 (d0 + 1) h1 h2)
      else none
    else none
  let alldiff : IntConstraint nv := alldifferent (_root_.Vector.ofFn id)
  ⟨nv, langford_bounds n 2 ++ spacing ++ [alldiff]⟩

-- L(2,6): UNSAT (6 ≡ 2 mod 4). veripb benchmark `langford6`.
def langford_2_6 : IntCSP := langford_2n_csp 6

-- L(2,9): UNSAT (9 ≡ 1 mod 4). veripb benchmark `langford9`.
def langford_2_9 : IntCSP := langford_2n_csp 9
