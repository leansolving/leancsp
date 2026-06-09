import CSP.L2S.Backends.PB.Adapter
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

/-! ### The signature and the linear `≤` constraint list -/

/-- The PB signature: 20 Boolean placement variables over `{0,1}`.
    Definitionally equal to `toCSPSig mutilatedChessboard (fun _ => 0) (fun _ => 1) _`. -/
def mcSig : CSPSig where
  nInt := 20
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The linear `≤` core fed to `unsat_of_pb`: the two `≤` halves of each cell's
    exactly-one constraint. -/
def mcLin : List (List (Int × Fin 20) × Int) :=
  [
    ([(1, (0 : Fin 20)), (1, (1 : Fin 20))], 1),
    ([(-1, (0 : Fin 20)), (-1, (1 : Fin 20))], -1),
    ([(1, (0 : Fin 20)), (1, (2 : Fin 20)), (1, (3 : Fin 20))], 1),
    ([(-1, (0 : Fin 20)), (-1, (2 : Fin 20)), (-1, (3 : Fin 20))], -1),
    ([(1, (2 : Fin 20)), (1, (4 : Fin 20))], 1),
    ([(-1, (2 : Fin 20)), (-1, (4 : Fin 20))], -1),
    ([(1, (5 : Fin 20)), (1, (6 : Fin 20))], 1),
    ([(-1, (5 : Fin 20)), (-1, (6 : Fin 20))], -1),
    ([(1, (1 : Fin 20)), (1, (5 : Fin 20)), (1, (7 : Fin 20)), (1, (8 : Fin 20))], 1),
    ([(-1, (1 : Fin 20)), (-1, (5 : Fin 20)), (-1, (7 : Fin 20)), (-1, (8 : Fin 20))], -1),
    ([(1, (3 : Fin 20)), (1, (7 : Fin 20)), (1, (9 : Fin 20)), (1, (10 : Fin 20))], 1),
    ([(-1, (3 : Fin 20)), (-1, (7 : Fin 20)), (-1, (9 : Fin 20)), (-1, (10 : Fin 20))], -1),
    ([(1, (4 : Fin 20)), (1, (9 : Fin 20)), (1, (11 : Fin 20))], 1),
    ([(-1, (4 : Fin 20)), (-1, (9 : Fin 20)), (-1, (11 : Fin 20))], -1),
    ([(1, (6 : Fin 20)), (1, (12 : Fin 20)), (1, (13 : Fin 20))], 1),
    ([(-1, (6 : Fin 20)), (-1, (12 : Fin 20)), (-1, (13 : Fin 20))], -1),
    ([(1, (8 : Fin 20)), (1, (12 : Fin 20)), (1, (14 : Fin 20)), (1, (15 : Fin 20))], 1),
    ([(-1, (8 : Fin 20)), (-1, (12 : Fin 20)), (-1, (14 : Fin 20)), (-1, (15 : Fin 20))], -1),
    ([(1, (10 : Fin 20)), (1, (14 : Fin 20)), (1, (16 : Fin 20)), (1, (17 : Fin 20))], 1),
    ([(-1, (10 : Fin 20)), (-1, (14 : Fin 20)), (-1, (16 : Fin 20)), (-1, (17 : Fin 20))], -1),
    ([(1, (11 : Fin 20)), (1, (16 : Fin 20))], 1),
    ([(-1, (11 : Fin 20)), (-1, (16 : Fin 20))], -1),
    ([(1, (13 : Fin 20)), (1, (18 : Fin 20))], 1),
    ([(-1, (13 : Fin 20)), (-1, (18 : Fin 20))], -1),
    ([(1, (15 : Fin 20)), (1, (18 : Fin 20)), (1, (19 : Fin 20))], 1),
    ([(-1, (15 : Fin 20)), (-1, (18 : Fin 20)), (-1, (19 : Fin 20))], -1),
    ([(1, (17 : Fin 20)), (1, (19 : Fin 20))], 1),
    ([(-1, (17 : Fin 20)), (-1, (19 : Fin 20))], -1)
  ]

/-! ### Bridges from a solution to the linear facts -/

/-- Every placement variable has its `bound 0 1` constraint in the CSP. -/
theorem mc_hbound (i : Fin mutilatedChessboard.num_vars) :
    bound i 0 1 ∈ mutilatedChessboard.constraints := by
  show bound i 0 1 ∈ ((List.finRange 20).map (fun i => bound i 0 1)) ++ _
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- Every linear `≤` fact in `mcLin` follows from any solution: each cell's `sum_eq … = 1`
    gives `Σ covering placements = 1`, whose two `≤` halves are the `mcLin` entries. -/
theorem mc_hlin (a : IntAssignment 20) (hsol : mutilatedChessboard.isSolutionInt a) :
    ∀ c ∈ mcLin, (c.1.map (fun p => p.1 * a p.2)).sum ≤ c.2 := by
  unfold IntCSP.isSolutionInt mutilatedChessboard at hsol
  simp only [List.forall_mem_append, List.forall_mem_cons] at hsol
  obtain ⟨_hbounds, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, _⟩ := hsol
  have hs0 := sum_eq_sat ⟨#[0, 1], rfl⟩ 1 a h0
  simp at hs0
  have hs1 := sum_eq_sat ⟨#[0, 2, 3], rfl⟩ 1 a h1
  simp at hs1
  have hs2 := sum_eq_sat ⟨#[2, 4], rfl⟩ 1 a h2
  simp at hs2
  have hs3 := sum_eq_sat ⟨#[5, 6], rfl⟩ 1 a h3
  simp at hs3
  have hs4 := sum_eq_sat ⟨#[1, 5, 7, 8], rfl⟩ 1 a h4
  simp at hs4
  have hs5 := sum_eq_sat ⟨#[3, 7, 9, 10], rfl⟩ 1 a h5
  simp at hs5
  have hs6 := sum_eq_sat ⟨#[4, 9, 11], rfl⟩ 1 a h6
  simp at hs6
  have hs7 := sum_eq_sat ⟨#[6, 12, 13], rfl⟩ 1 a h7
  simp at hs7
  have hs8 := sum_eq_sat ⟨#[8, 12, 14, 15], rfl⟩ 1 a h8
  simp at hs8
  have hs9 := sum_eq_sat ⟨#[10, 14, 16, 17], rfl⟩ 1 a h9
  simp at hs9
  have hs10 := sum_eq_sat ⟨#[11, 16], rfl⟩ 1 a h10
  simp at hs10
  have hs11 := sum_eq_sat ⟨#[13, 18], rfl⟩ 1 a h11
  simp at hs11
  have hs12 := sum_eq_sat ⟨#[15, 18, 19], rfl⟩ 1 a h12
  simp at hs12
  have hs13 := sum_eq_sat ⟨#[17, 19], rfl⟩ 1 a h13
  simp at hs13
  intro c hc
  simp only [mcLin, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
    linarith [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13]

/-! ### The certificate and the end-to-end theorem -/

/-- The veripb-elaborated kernel proof of UNSAT for `mcLin`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The 20 placements map to OPB `x1 .. x20`;
    the single `pol` step is the colour-counting linear combination. -/
def mcKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 28;
rup >= 0 : ~ ;
pol 29 2 1000000000000000 * + 3 1000000000000000 * + 6 1000000000000000 * + 8 1000000000000000 * + 9 1000000000000000 * + 12 1000000000000000 * + 13 1000000000000000 * + 15 1000000000000000 * + 18 1000000000000000 * + 19 1000000000000000 * + 22 1000000000000000 * + 24 1000000000000000 * + 25 1000000000000000 * + 28 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 30;
end pseudo-Boolean proof;
"

/-- The PB encoding of the mutilated chessboard's exact-cover query is unsatisfiable —
    established by the external PB certificate, kernel-checked through PBLean's verified
    reflection checker (`native_decide` runs the checker; RoundingSat / veripb / the
    serializer are untrusted). -/
theorem mc_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((encodeLinear mcSig mcLin).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 20 mcKernelProof (by native_decide)

/-- **End-to-end mutilated-chessboard UNSAT.** A `4 × 4` board with two opposite
    (black) corners removed cannot be tiled by dominoes: the 6 black and 8 white
    remaining cells cannot be matched one-to-one.  Discharged through the verified PB
    pipeline — the `sum_eq` bridge turns any solution into the per-cell exactly-one facts,
    the `unsat_of_pb` spine order-encodes their `≤` halves via `encodeLinear`, and the
    committed certificate `mc_formulaUnsat` derives the colour-count contradiction. -/
theorem mutilated_chessboard_unsat : ¬ mutilatedChessboard.isSatisfiableInt := by
  refine unsat_of_pb mutilatedChessboard (fun _ => 0) (fun _ => 1) (fun _ => by norm_num)
    mc_hbound mcLin mc_hlin ?_
  show VeriPB.Reflect.formulaUnsat
    ((encodeLinear mcSig mcLin).toArray.map PBConstr.toNatConstr)
  exact mc_formulaUnsat

end CSP.L2S.PB.MutilatedChessboard
