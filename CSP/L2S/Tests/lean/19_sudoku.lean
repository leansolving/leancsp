import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Sudoku Puzzle
CSPLib Problem 057

## Problem Description
Fill an n×n grid with digits 1..n such that:
- Each row contains all digits 1..n
- Each column contains all digits 1..n
- Each s×s box contains all digits 1..n (where n = s²)

Standard Sudoku: n=9, s=3

## CSP Formulation
- **Variables**: n² variables (grid positions), domain [1, n]
- **Variable Indexing**: grid[r,c] maps to variable index `n*r + c` where r,c ∈ [0,n-1]
- **Constraints**:
  1. Bounds: all variables in [1, n]
  2. Row alldifferent: n constraints (one per row)
  3. Column alldifferent: n constraints (one per column)
  4. Box alldifferent: n constraints (one per s×s box)

## Parametrized Design
- `sudoku_csp(n, s)` - general formulation for any n×n grid with s×s boxes
- `sudoku_9` - standard 9×9 Sudoku instance

## Source
CSPLib Problem 057 (standard 9×9 Sudoku)
-/

-- Helper function: get all variables in row i (for n×n grid)
def row_variables (n : ℕ) (i : Fin n) : _root_.Vector (VarType (n*n)) n :=
  _root_.Vector.ofFn (fun j => ⟨i.val * n + j.val, by
    have h1 : i.val < n := i.isLt
    have h2 : j.val < n := j.isLt
    calc i.val * n + j.val
        < i.val * n + n := Nat.add_lt_add_left h2 _
      _ = (i.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩)

-- Helper function: get all variables in column j (for n×n grid)
def col_variables (n : ℕ) (j : Fin n) : _root_.Vector (VarType (n*n)) n :=
  _root_.Vector.ofFn (fun i => ⟨i.val * n + j.val, by
    have h1 : i.val < n := i.isLt
    have h2 : j.val < n := j.isLt
    calc i.val * n + j.val
        < i.val * n + n := Nat.add_lt_add_left h2 _
      _ = (i.val + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h1)⟩)

-- Helper function: get all variables in box (br, bc) where br,bc ∈ [0, s-1]
-- Box contains cells at (s*br+di, s*bc+dj) for di,dj ∈ [0, s-1]
-- Uses filter approach like diagonal constraints in NQueens
def box_variables (n s : ℕ) (br bc : Fin s) : List (VarType (n*n)) :=
  (List.finRange (n*n)).filter fun v =>
    let row := v.val / n
    let col := v.val % n
    (row / s = br.val) && (col / s = bc.val)

-- Helper to convert list to vector
private def listToVector {α : Type*} (l : List α) : _root_.Vector α l.length :=
  ⟨l.toArray, by simp [List.size_toArray]⟩

-- Parametrized Sudoku CSP for n×n grid with s×s boxes (n should equal s²)
def sudoku_csp (n s : ℕ) : IntCSP :=
  let bounds_list := (List.finRange (n*n)).map fun i => bound i 1 n
  -- Row constraints: alldifferent for each row
  let row_constraints := (List.finRange n).map fun i =>
    alldifferent (row_variables n i)
  -- Column constraints: alldifferent for each column
  let col_constraints := (List.finRange n).map fun j =>
    alldifferent (col_variables n j)
  -- Box constraints: alldifferent for each s×s box
  let box_constraints := (List.finRange s).flatMap fun br =>
    (List.finRange s).filterMap fun bc =>
      let cells := box_variables n s br bc
      match cells with
      | [] => none
      | _ => some (alldifferent (listToVector cells))
  ⟨n*n, bounds_list ++ row_constraints ++ col_constraints ++ box_constraints⟩

-- Standard 9×9 Sudoku instance
def sudoku_9 : IntCSP :=
  sudoku_csp 9 3

def sudoku_4 : IntCSP :=
  sudoku_csp 4 2

def main : IO Unit := do
  saveAllBackendsAutoTimed sudoku_9
