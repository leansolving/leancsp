import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Constraints

namespace CSP.L2S.PB.MutilatedChessboard

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the mutilated chessboard

Remove two **opposite (same-colour) corners** from a `4 × 4` board and ask whether the
remaining `14` cells can be tiled by dominoes.  Colour the board like a chessboard: each
domino covers exactly one black and one white cell, so a tiling needs equally many of
each.  But the two removed corners `(0,0)` and `(3,3)` are both black, leaving `6` black
and `8` white cells — an imbalance of `2`.  No tiling exists.  This is the classic
**mutilated-chessboard** parity/counting argument, and it is *provably* UNSAT (no probing
needed).  Unlike the degenerate `2 × n` cases, every remaining cell here has degree `≥ 2`,
so the impossibility is the genuine colour count, not mere unit propagation.

## Encoding (exact cover)

`mutilatedChessboard` is modelled directly (it is not a pre-existing corpus problem):
one Boolean `{0,1}` variable per legal **domino placement** (a pair of orthogonally
adjacent remaining cells) — `20` placements in all — and, for each of the `14` remaining
cells, an exactly-one constraint `Σ placements covering the cell = 1` (`sum_eq`).  A
solution is a perfect domino tiling.

Every constraint is linear over `{0,1}`: each `sum_eq … = 1` splits into the two `≤`
halves `Σ ≤ 1` and `Σ ≥ 1`, so the proof rides the clean `unsat_of_pb` spine
(`Adapter.lean`) — no auxiliary variables, no order-encoding monotonicity (every domain is
width-1).  The cutting-planes certificate is the colour count itself: summing the `≤ 1`
halves over the `6` black cells bounds the placed dominoes by `6`, while summing the `≥ 1`
halves over the `8` white cells forces `≥ 8` — a one-line contradiction.

Cells are taken in row-major order over the `14` remaining squares; placement variables
`0 .. 19` are the orthogonally-adjacent cell pairs, in row-major scan order.
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
