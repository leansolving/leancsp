import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# N-Queens

Place n queens on n×n chessboard with no attacks.

Variables: n (one per column), domain 1..n (row)
Constraints: No shared rows, positive diagonals, or negative diagonals

Fully parametrized for any board size.
-/

-- Helper to create bound constraints for N-Queens
def queens_bounds (n : ℕ) : List (IntConstraint n) :=
  (List.finRange n).map fun i => bound i 1 n

-- General N-Queens CSP - parametrized for any board size
def nqueens_csp (n : ℕ) : IntCSP :=
  ⟨n, queens_bounds n ++ [
    alldifferent (_root_.Vector.ofFn id),
    alldifferent_diag_pos n,
    alldifferent_diag_neg n
  ]⟩

-- Specific instance:
def queens_inst : IntCSP :=
  nqueens_csp 30
