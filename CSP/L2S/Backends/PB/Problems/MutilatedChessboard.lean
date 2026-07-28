import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Constraints

namespace CSP.L2S.PB.MutilatedChessboard

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for the mutilated chessboard

Remove two opposite (same-colour) corners from a `4 × 4` board: can the remaining `14`
cells be tiled by dominoes?  Each domino covers one black and one white cell, but the
removed corners `(0,0)` and `(3,3)` are both black, leaving `6` black and `8` white cells.
No tiling exists.

Encoding (exact cover): one `{0,1}` variable per legal domino placement — a pair of
orthogonally adjacent remaining cells, `20` in all — plus an exactly-one constraint
`Σ placements covering the cell = 1` for each of the `14` cells.  A solution is a perfect
tiling.

Every constraint is linear over `{0,1}`, so there are no auxiliary variables and no
order-encoding monotonicity.  The cutting-planes certificate is the colour count itself:
summing the `≤ 1` halves over the `6` black cells bounds the placed dominoes by `6`, while
summing the `≥ 1` halves over the `8` white cells forces `≥ 8`.

Cells are taken in row-major order; placement variables `0 .. 19` are the adjacent cell
pairs, also in row-major scan order.
-/

/-! ### The CSP -/

/-- The 20 domino-placement variables, one per pair of orthogonally adjacent remaining
    cells, each constrained to `{0,1}`; plus one exactly-one (`sum_eq … = 1`) constraint
    per remaining cell (its covering placements).  A solution is a perfect tiling. -/
def mutilatedChessboard : IntCSP :=
  ⟨20, ((List.finRange 20).map (fun i => bound i 0 1))
      ++ [
    -- cell (0, 1) (white)
    sum_eq (⟨#[0, 1], rfl⟩ : _root_.Vector (VarType 20) 2) 1,
    -- cell (0, 2) (black)
    sum_eq (⟨#[0, 2, 3], rfl⟩ : _root_.Vector (VarType 20) 3) 1,
    -- cell (0, 3) (white)
    sum_eq (⟨#[2, 4], rfl⟩ : _root_.Vector (VarType 20) 2) 1,
    -- cell (1, 0) (white)
    sum_eq (⟨#[5, 6], rfl⟩ : _root_.Vector (VarType 20) 2) 1,
    -- cell (1, 1) (black)
    sum_eq (⟨#[1, 5, 7, 8], rfl⟩ : _root_.Vector (VarType 20) 4) 1,
    -- cell (1, 2) (white)
    sum_eq (⟨#[3, 7, 9, 10], rfl⟩ : _root_.Vector (VarType 20) 4) 1,
    -- cell (1, 3) (black)
    sum_eq (⟨#[4, 9, 11], rfl⟩ : _root_.Vector (VarType 20) 3) 1,
    -- cell (2, 0) (black)
    sum_eq (⟨#[6, 12, 13], rfl⟩ : _root_.Vector (VarType 20) 3) 1,
    -- cell (2, 1) (white)
    sum_eq (⟨#[8, 12, 14, 15], rfl⟩ : _root_.Vector (VarType 20) 4) 1,
    -- cell (2, 2) (black)
    sum_eq (⟨#[10, 14, 16, 17], rfl⟩ : _root_.Vector (VarType 20) 4) 1,
    -- cell (2, 3) (white)
    sum_eq (⟨#[11, 16], rfl⟩ : _root_.Vector (VarType 20) 2) 1,
    -- cell (3, 0) (white)
    sum_eq (⟨#[13, 18], rfl⟩ : _root_.Vector (VarType 20) 2) 1,
    -- cell (3, 1) (black)
    sum_eq (⟨#[15, 18, 19], rfl⟩ : _root_.Vector (VarType 20) 3) 1,
    -- cell (3, 2) (white)
    sum_eq (⟨#[17, 19], rfl⟩ : _root_.Vector (VarType 20) 2) 1
      ]⟩

/-- **UNSAT via the generic pipeline.** -/
theorem mutilated_chessboard_unsat :
    ¬ mutilatedChessboard.isSatisfiableInt :=
  csp_unsat_file mutilatedChessboard 20 "certs/mutilated.pbp"

end CSP.L2S.PB.MutilatedChessboard
