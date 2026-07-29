import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Sudoku

Fill an `n×n` grid (`n = s²`) with digits `1..n` so every row, column and `s×s` box
contains each digit once.  Variables are the `n²` cells, with `grid[r,c]` at index
`n*r + c`, and one `alldifferent` per row, column and box.

`sudoku_csp n s` is the general form; `sudoku_9` the standard instance.
CSPLib problem 057.
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
