import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Proofs.PatternBridges
import CSP.L2S.Backends.PB.Bench.Generators
import Mathlib.Tactic.Linarith

open CSP.L2S CSP.L2S.IntCSP Bench

/-!
# Orientation-based mutilated chessboard ≡ edge / exact-cover model

The project models the `2k×2k` mutilated chessboard (two opposite same-colour
corners removed) as the **edge / exact-cover** CSP `Bench.gen_mutilated k`
(`Generators.lean`): one `{0,1}` variable per potential domino, an
`exactly_k = 1` per present cell.

This file gives a second, **orientation-based** model `gen_orient k` — every
present cell carries a direction variable `U/D/L/R` to its domino partner, with
reciprocity (`if c = RIGHT then right-neighbour = LEFT`) — and proves it
`piEquivalent` to `gen_mutilated k` (`CSP/L2S/Equivalence.lean`), exactly as the
sibling equivalence proofs (`NQueensEquivalence`, …) do.  Coverage is *free*: in
any solution each cell points to one present neighbour and reciprocity forces
that neighbour to point back, so the points-to relation is a fixed-point-free
involution = a perfect matching.

The orientation model is never PB-encoded (its `if_then` constraints are outside
the PB encoder); its UNSAT is obtained purely from `gen_mutilated k`'s UNSAT via
`equisatisfiable` (`mutilated_orient_unsat_of_edge_unsat`).

Direction codes: `none = 0`, `U = 1`, `D = 2`, `L = 3`, `R = 4`
(`0` is reserved for the removed corners, which point nowhere).
-/

namespace CSP.L2S.MutilatedOrient

/-! ### The orientation CSP -/

/-- The `2k×2k` orientation CSP: one variable per cell (`cell r c = r*N + c`,
    `N = 2k`), domain `{1,2,3,4}` = `U/D/L/R`; removed corners pinned to `0` (= none,
    not a direction).  For each present cell and direction, either `ne_const` (the
    neighbour is off-board or removed — illegal) or `if_then` reciprocity. -/
def gen_orient (k : ℕ) : IntCSP :=
  let N := 2 * k
  let bounds : List (IntConstraint (2 * k * (2 * k))) :=
    (List.range N).flatMap fun r =>
      (List.range N).map fun c =>
        if Bench.mutRemoved N r c
        then IntConstraint.bound (r * N + c) 0 0
        else IntConstraint.bound (r * N + c) 1 4
  let recip : List (IntConstraint (2 * k * (2 * k))) :=
    (List.range N).flatMap fun r =>
      (List.range N).flatMap fun c =>
        if Bench.mutRemoved N r c then ([] : List (IntConstraint (2 * k * (2 * k)))) else
          (if decide (c + 1 < N) && !Bench.mutRemoved N r (c + 1)
             then [IntConstraint.if_then (r * N + c) 4 (r * N + (c + 1)) 3]
             else [IntConstraint.ne_const (r * N + c) 4]) ++
          (if decide (0 < c) && !Bench.mutRemoved N r (c - 1)
             then [IntConstraint.if_then (r * N + c) 3 (r * N + (c - 1)) 4]
             else [IntConstraint.ne_const (r * N + c) 3]) ++
          (if decide (r + 1 < N) && !Bench.mutRemoved N (r + 1) c
             then [IntConstraint.if_then (r * N + c) 2 ((r + 1) * N + c) 1]
             else [IntConstraint.ne_const (r * N + c) 2]) ++
          (if decide (0 < r) && !Bench.mutRemoved N (r - 1) c
             then [IntConstraint.if_then (r * N + c) 1 ((r - 1) * N + c) 2]
             else [IntConstraint.ne_const (r * N + c) 1])
  ⟨2 * k * (2 * k), bounds ++ recip⟩

/-! ### The projection `gen_orient → gen_mutilated` -/

/-- Read edge variable `i` of a `gen_mutilated k` assignment (guarded; `0`
    off-range). -/
def edgeVal (k : ℕ) (x : IntAssignment (2 * (2 * k) * (2 * k - 1))) (i : ℕ) : ℤ :=
  if h : i < 2 * (2 * k) * (2 * k - 1) then x ⟨i, h⟩ else 0

/-- Projection `π`: an orientation assignment ↦ the edge/matching assignment.
    Edge `e` (matching `gen_mutilated`'s indexing: horizontal `h(r,c)=r*(N-1)+c`
    for `e < nH = N*(N-1)`, vertical `v(r,c)=nH+r*N+c` otherwise) is selected iff
    its *designated* endpoint points along it — the left cell points `R = 4` for a
    horizontal, the upper cell points `D = 2` for a vertical. -/
def piMap (k : ℕ) (a : IntAssignment (2 * k * (2 * k))) :
    IntAssignment (2 * (2 * k) * (2 * k - 1)) :=
  fun e =>
    let nH := (2 * k) * (2 * k - 1)
    let r := if e.val < nH then e.val / (2 * k - 1) else (e.val - nH) / (2 * k)
    let c := if e.val < nH then e.val % (2 * k - 1) else (e.val - nH) % (2 * k)
    let dir : ℤ := if e.val < nH then 4 else 2
    if h : r * (2 * k) + c < 2 * k * (2 * k)
    then (if a ⟨r * (2 * k) + c, h⟩ = dir then 1 else 0)
    else 0

/-- Backward witness: a `gen_mutilated k` matching ↦ the orientation assignment
    pointing each present cell at its matched partner (removed corner ↦ `0`). -/
def liftOrient (k : ℕ) (x : IntAssignment (2 * (2 * k) * (2 * k - 1))) :
    IntAssignment (2 * k * (2 * k)) :=
  fun p =>
    let N := 2 * k
    let nH := N * (N - 1)
    let r := p.val / N
    let c := p.val % N
    if Bench.mutRemoved N r c then 0
    else
      if decide (c + 1 < N) && (edgeVal k x (r * (N - 1) + c) == 1) then 4        -- R
      else if decide (0 < c) && (edgeVal k x (r * (N - 1) + (c - 1)) == 1) then 3 -- L
      else if decide (r + 1 < N) && (edgeVal k x (nH + r * N + c) == 1) then 2    -- D
      else if decide (0 < r) && (edgeVal k x (nH + (r - 1) * N + c) == 1) then 1  -- U
      else 0

/-! ### `piMap` roundtrip on the two edge kinds -/

/-- Value of `piMap k a` on a horizontal edge `h(r,c) = r*(N-1)+c` (`N = 2k`):
    `1` iff the left cell `(r,c)` points `R = 4`. -/
private lemma valAt_piMap_h (k : ℕ) (hk : 2 ≤ k) (a : IntAssignment (2 * k * (2 * k)))
    (r c : ℕ) (hr : r < 2 * k) (hc : c + 1 < 2 * k) :
    valAt (piMap k a) (r * (2 * k - 1) + c) = (if valAt a (r * (2 * k) + c) = 4 then 1 else 0) := by
  have hN1 : 0 < 2 * k - 1 := by omega
  have hcN1 : c < 2 * k - 1 := by omega
  have hdiv : (r * (2 * k - 1) + c) / (2 * k - 1) = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN1, Nat.div_eq_of_lt hcN1, Nat.zero_add]
  have hmod : (r * (2 * k - 1) + c) % (2 * k - 1) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcN1]
  have hei_nH : r * (2 * k - 1) + c < (2 * k) * (2 * k - 1) := by
    have h1 : (r + 1) * (2 * k - 1) ≤ (2 * k) * (2 * k - 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : r * (2 * k - 1) + (2 * k - 1) = (r + 1) * (2 * k - 1) := by ring
    omega
  have hei_np : r * (2 * k - 1) + c < 2 * (2 * k) * (2 * k - 1) := by
    have : (2 * k) * (2 * k - 1) ≤ 2 * (2 * k) * (2 * k - 1) := by nlinarith
    omega
  have hcell : r * (2 * k) + c < 2 * k * (2 * k) := by
    have h1 : (r + 1) * (2 * k) ≤ (2 * k) * (2 * k) := Nat.mul_le_mul_right _ (by omega)
    have h2 : r * (2 * k) + (2 * k) = (r + 1) * (2 * k) := by ring
    omega
  simp only [valAt]
  rw [dif_pos hei_np]
  simp only [piMap]
  simp only [if_pos hei_nH, hdiv, hmod]
  simp only [dif_pos hcell]

/-- Value of `piMap k a` on a vertical edge `v(r,c) = N*(N-1)+r*N+c` (`N = 2k`):
    `1` iff the upper cell `(r,c)` points `D = 2`. -/
private lemma valAt_piMap_v (k : ℕ) (hk : 2 ≤ k) (a : IntAssignment (2 * k * (2 * k)))
    (r c : ℕ) (hr : r + 1 < 2 * k) (hc : c < 2 * k) :
    valAt (piMap k a) ((2 * k) * (2 * k - 1) + r * (2 * k) + c)
      = (if valAt a (r * (2 * k) + c) = 2 then 1 else 0) := by
  have hNpos : 0 < 2 * k := by omega
  have hdiv : (r * (2 * k) + c) / (2 * k) = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hNpos, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (r * (2 * k) + c) % (2 * k) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hcell : r * (2 * k) + c < 2 * k * (2 * k) := by
    have h1 : (r + 1) * (2 * k) ≤ (2 * k) * (2 * k) := Nat.mul_le_mul_right _ (by omega)
    have h2 : r * (2 * k) + (2 * k) = (r + 1) * (2 * k) := by ring
    omega
  have hsub : (2 * k) * (2 * k - 1) + r * (2 * k) + c - (2 * k) * (2 * k - 1) = r * (2 * k) + c := by
    omega
  have hge : ¬ ((2 * k) * (2 * k - 1) + r * (2 * k) + c < (2 * k) * (2 * k - 1)) := by omega
  have hei_np : (2 * k) * (2 * k - 1) + r * (2 * k) + c < 2 * (2 * k) * (2 * k - 1) := by
    have hcellH : r * (2 * k) + c < (2 * k) * (2 * k - 1) := by
      have h1 : (r + 1) * (2 * k) ≤ (2 * k - 1) * (2 * k) := Nat.mul_le_mul_right _ (by omega)
      have h2 : r * (2 * k) + (2 * k) = (r + 1) * (2 * k) := by ring
      have h3 : (2 * k - 1) * (2 * k) = (2 * k) * (2 * k - 1) := by ring
      omega
    have h4 : 2 * (2 * k) * (2 * k - 1) = (2 * k) * (2 * k - 1) + (2 * k) * (2 * k - 1) := by ring
    omega
  simp only [valAt]
  rw [dif_pos hei_np]
  simp only [piMap]
  simp only [if_neg hge, hsub, hdiv, hmod]
  simp only [dif_pos hcell]

/-! ### Membership in `gen_orient`'s constraint list -/

/-- `gen_orient`'s constraints, with the `let`s unfolded. -/
private lemma orient_constraints_def (k : ℕ) :
    (gen_orient k).constraints =
      ((List.range (2 * k)).flatMap fun r => (List.range (2 * k)).map fun c =>
        if Bench.mutRemoved (2 * k) r c then IntConstraint.bound (r * (2 * k) + c) 0 0
        else IntConstraint.bound (r * (2 * k) + c) 1 4)
      ++ ((List.range (2 * k)).flatMap fun r => (List.range (2 * k)).flatMap fun c =>
        if Bench.mutRemoved (2 * k) r c then ([] : List (IntConstraint (2 * k * (2 * k)))) else
          (if decide (c + 1 < 2 * k) && !Bench.mutRemoved (2 * k) r (c + 1)
             then [IntConstraint.if_then (r * (2 * k) + c) 4 (r * (2 * k) + (c + 1)) 3]
             else [IntConstraint.ne_const (r * (2 * k) + c) 4]) ++
          (if decide (0 < c) && !Bench.mutRemoved (2 * k) r (c - 1)
             then [IntConstraint.if_then (r * (2 * k) + c) 3 (r * (2 * k) + (c - 1)) 4]
             else [IntConstraint.ne_const (r * (2 * k) + c) 3]) ++
          (if decide (r + 1 < 2 * k) && !Bench.mutRemoved (2 * k) (r + 1) c
             then [IntConstraint.if_then (r * (2 * k) + c) 2 ((r + 1) * (2 * k) + c) 1]
             else [IntConstraint.ne_const (r * (2 * k) + c) 2]) ++
          (if decide (0 < r) && !Bench.mutRemoved (2 * k) (r - 1) c
             then [IntConstraint.if_then (r * (2 * k) + c) 1 ((r - 1) * (2 * k) + c) 2]
             else [IntConstraint.ne_const (r * (2 * k) + c) 1])) := rfl

/-- A present cell's value lies in `[1,4]`. -/
private lemma orient_range (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) :
    1 ≤ valAt a (r * (2 * k) + c) ∧ valAt a (r * (2 * k) + c) ≤ 4 := by
  have hmem : IntConstraint.bound (r * (2 * k) + c) 1 4 ∈ (gen_orient k).constraints := by
    rw [orient_constraints_def]
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
    have hfc : (if Bench.mutRemoved (2 * k) r c
        then (IntConstraint.bound (r * (2 * k) + c) 0 0 : IntConstraint (2 * k * (2 * k)))
        else IntConstraint.bound (r * (2 * k) + c) 1 4) = IntConstraint.bound (r * (2 * k) + c) 1 4 := by
      simp [hpres]
    exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, hfc⟩
  have := ha _ hmem
  simpa only [satisfiesConstraintInt, patternHolds] using this

/-- A removed cell's value is pinned to `0`. -/
private lemma orient_removed_zero (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hrem : Bench.mutRemoved (2 * k) r c = true) :
    valAt a (r * (2 * k) + c) = 0 := by
  have hmem : IntConstraint.bound (r * (2 * k) + c) 0 0 ∈ (gen_orient k).constraints := by
    rw [orient_constraints_def]
    refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
    have hfc : (if Bench.mutRemoved (2 * k) r c
        then (IntConstraint.bound (r * (2 * k) + c) 0 0 : IntConstraint (2 * k * (2 * k)))
        else IntConstraint.bound (r * (2 * k) + c) 1 4) = IntConstraint.bound (r * (2 * k) + c) 0 0 := by
      simp [hrem]
    exact List.mem_map.mpr ⟨c, List.mem_range.mpr hc, hfc⟩
  have hb : (0 : ℤ) ≤ valAt a (r * (2 * k) + c) ∧ valAt a (r * (2 * k) + c) ≤ 0 := by
    have := ha _ hmem
    simpa only [satisfiesConstraintInt, patternHolds] using this
  omega

/-- **R reciprocity / legality.** If a present cell points `R = 4`, then `R` is legal
    (the right neighbour exists and is present) and that neighbour points `L = 3`. -/
private lemma orient_R (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) (hd : valAt a (r * (2 * k) + c) = 4) :
    c + 1 < 2 * k ∧ Bench.mutRemoved (2 * k) r (c + 1) = false
      ∧ valAt a (r * (2 * k) + (c + 1)) = 3 := by
  by_cases hleg : (decide (c + 1 < 2 * k) && !Bench.mutRemoved (2 * k) r (c + 1)) = true
  · have hlegit : c + 1 < 2 * k ∧ Bench.mutRemoved (2 * k) r (c + 1) = false := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hleg
      exact hleg
    have hmem : IntConstraint.if_then (r * (2 * k) + c) 4 (r * (2 * k) + (c + 1)) 3
        ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      rw [if_pos hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    rcases hsat with hne | hyes
    · exact absurd hd hne
    · exact ⟨hlegit.1, hlegit.2, hyes⟩
  · exfalso
    have hmem : IntConstraint.ne_const (r * (2 * k) + c) 4 ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_))
      rw [if_neg hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    exact hsat hd

/-- **L reciprocity / legality.** If a present cell points `L = 3`, then `L` is legal
    and the left neighbour points `R = 4`. -/
private lemma orient_L (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) (hd : valAt a (r * (2 * k) + c) = 3) :
    0 < c ∧ Bench.mutRemoved (2 * k) r (c - 1) = false
      ∧ valAt a (r * (2 * k) + (c - 1)) = 4 := by
  by_cases hleg : (decide (0 < c) && !Bench.mutRemoved (2 * k) r (c - 1)) = true
  · have hlegit : 0 < c ∧ Bench.mutRemoved (2 * k) r (c - 1) = false := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hleg
      exact hleg
    have hmem : IntConstraint.if_then (r * (2 * k) + c) 3 (r * (2 * k) + (c - 1)) 4
        ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      rw [if_pos hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    rcases hsat with hne | hyes
    · exact absurd hd hne
    · exact ⟨hlegit.1, hlegit.2, hyes⟩
  · exfalso
    have hmem : IntConstraint.ne_const (r * (2 * k) + c) 3 ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
      rw [if_neg hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    exact hsat hd

/-- **D reciprocity / legality.** If a present cell points `D = 2`, then `D` is legal
    and the lower neighbour points `U = 1`. -/
private lemma orient_D (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) (hd : valAt a (r * (2 * k) + c) = 2) :
    r + 1 < 2 * k ∧ Bench.mutRemoved (2 * k) (r + 1) c = false
      ∧ valAt a ((r + 1) * (2 * k) + c) = 1 := by
  by_cases hleg : (decide (r + 1 < 2 * k) && !Bench.mutRemoved (2 * k) (r + 1) c) = true
  · have hlegit : r + 1 < 2 * k ∧ Bench.mutRemoved (2 * k) (r + 1) c = false := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hleg
      exact hleg
    have hmem : IntConstraint.if_then (r * (2 * k) + c) 2 ((r + 1) * (2 * k) + c) 1
        ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [if_pos hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    rcases hsat with hne | hyes
    · exact absurd hd hne
    · exact ⟨hlegit.1, hlegit.2, hyes⟩
  · exfalso
    have hmem : IntConstraint.ne_const (r * (2 * k) + c) 2 ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      rw [if_neg hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    exact hsat hd

/-- **U reciprocity / legality.** If a present cell points `U = 1`, then `U` is legal
    and the upper neighbour points `D = 2`. -/
private lemma orient_U (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) (hd : valAt a (r * (2 * k) + c) = 1) :
    0 < r ∧ Bench.mutRemoved (2 * k) (r - 1) c = false
      ∧ valAt a ((r - 1) * (2 * k) + c) = 2 := by
  by_cases hleg : (decide (0 < r) && !Bench.mutRemoved (2 * k) (r - 1) c) = true
  · have hlegit : 0 < r ∧ Bench.mutRemoved (2 * k) (r - 1) c = false := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hleg
      exact hleg
    have hmem : IntConstraint.if_then (r * (2 * k) + c) 1 ((r - 1) * (2 * k) + c) 2
        ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_right _ ?_
      rw [if_pos hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    rcases hsat with hne | hyes
    · exact absurd hd hne
    · exact ⟨hlegit.1, hlegit.2, hyes⟩
  · exfalso
    have hmem : IntConstraint.ne_const (r * (2 * k) + c) 1 ∈ (gen_orient k).constraints := by
      rw [orient_constraints_def]
      refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
      refine List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
      rw [if_neg (by simp [hpres])]
      refine List.mem_append_right _ ?_
      rw [if_neg hleg]
      exact List.mem_singleton.mpr rfl
    have hsat := ha _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at hsat
    exact hsat hd

/-- The left neighbour of a cell that does not point `L = 3` cannot point `R = 4`
    (else reciprocity would force this cell to point `L`). -/
private lemma nbr_left_ne3 (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hcpos : 0 < c) (hne2 : valAt a (r * (2 * k) + c) ≠ 3) :
    valAt a (r * (2 * k) + (c - 1)) ≠ 4 := by
  intro h4
  by_cases hp : Bench.mutRemoved (2 * k) r (c - 1) = false
  · have hd := orient_R k a ha r (c - 1) hr (by omega) hp h4
    have hcc : c - 1 + 1 = c := by omega
    rw [hcc] at hd
    exact hne2 hd.2.2
  · have hrem : Bench.mutRemoved (2 * k) r (c - 1) = true := by
      cases hb : Bench.mutRemoved (2 * k) r (c - 1) with
      | false => exact absurd hb hp
      | true => rfl
    rw [orient_removed_zero k a ha r (c - 1) hr (by omega) hrem] at h4; omega

/-- The upper neighbour of a cell that does not point `U = 1` cannot point `D = 2`. -/
private lemma nbr_up_ne1 (k : ℕ) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hrpos : 0 < r) (hne0 : valAt a (r * (2 * k) + c) ≠ 1) :
    valAt a ((r - 1) * (2 * k) + c) ≠ 2 := by
  intro h2
  by_cases hp : Bench.mutRemoved (2 * k) (r - 1) c = false
  · have hd := orient_D k a ha (r - 1) c (by omega) hc hp h2
    have hrr : r - 1 + 1 = r := by omega
    rw [hrr] at hd
    exact hne0 hd.2.2
  · have hrem : Bench.mutRemoved (2 * k) (r - 1) c = true := by
      cases hb : Bench.mutRemoved (2 * k) (r - 1) c with
      | false => exact absurd hb hp
      | true => rfl
    rw [orient_removed_zero k a ha (r - 1) c (by omega) hc hrem] at h2; omega

/-- **The exact-cover constraint, forward.** For a present cell, exactly one incident
    edge is selected by `piMap k a`. -/
private lemma forward_cell (k : ℕ) (hk : 2 ≤ k) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) :
    ((Bench.mutIncident k r c).map (valAt (piMap k a))).sum = (1 : ℤ) := by
  have hcond : ∀ (P : Prop) [Decidable P] (e : ℕ),
      (List.map (valAt (piMap k a)) (if P then [e] else [])).sum
        = if P then valAt (piMap k a) e else 0 := by
    intro P _ e; split_ifs <;> simp
  simp only [Bench.mutIncident, List.map_append, List.sum_append, hcond]
  rw [show (if c + 1 < 2 * k then valAt (piMap k a) (r * (2 * k - 1) + c) else 0)
        = (if c + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (4 : ℤ) then (1 : ℤ) else 0)
           else 0) from by
        by_cases h : c + 1 < 2 * k
        · rw [if_pos h, if_pos h]; exact valAt_piMap_h k hk a r c hr h
        · rw [if_neg h, if_neg h],
      show (if 0 < c then valAt (piMap k a) (r * (2 * k - 1) + (c - 1)) else 0)
        = (if 0 < c then (if valAt a (r * (2 * k) + (c - 1)) = (4 : ℤ) then (1 : ℤ) else 0)
           else 0) from by
        by_cases h : 0 < c
        · rw [if_pos h, if_pos h]; exact valAt_piMap_h k hk a r (c - 1) hr (by omega)
        · rw [if_neg h, if_neg h],
      show (if r + 1 < 2 * k then valAt (piMap k a) (2 * k * (2 * k - 1) + r * (2 * k) + c) else 0)
        = (if r + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
           else 0) from by
        by_cases h : r + 1 < 2 * k
        · rw [if_pos h, if_pos h]; exact valAt_piMap_v k hk a r c h hc
        · rw [if_neg h, if_neg h],
      show (if 0 < r then valAt (piMap k a) (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) else 0)
        = (if 0 < r then (if valAt a ((r - 1) * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
           else 0) from by
        by_cases h : 0 < r
        · rw [if_pos h, if_pos h]; exact valAt_piMap_v k hk a (r - 1) c (by omega) hc
        · rw [if_neg h, if_neg h]]
  obtain ⟨hge, hle⟩ := orient_range k a ha r c hr hc hpres
  rcases (show valAt a (r * (2 * k) + c) = 1 ∨ valAt a (r * (2 * k) + c) = 2
      ∨ valAt a (r * (2 * k) + c) = 3 ∨ valAt a (r * (2 * k) + c) = 4 from by omega)
    with h | h | h | h
  · -- U : points up
    have hU := orient_U k a ha r c hr hc hpres h
    have t1 : (if c + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by simp [h]
    have t2 : (if 0 < c then (if valAt a (r * (2 * k) + (c - 1)) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by
      by_cases hcp : 0 < c
      · simp [hcp, nbr_left_ne3 k a ha r c hr hc hcp (by omega)]
      · simp [hcp]
    have t3 : (if r + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by simp [h]
    have t4 : (if 0 < r then (if valAt a ((r - 1) * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 1 := by simp [hU.1, hU.2.2]
    linarith [t1, t2, t3, t4]
  · -- D : points down
    have hD := orient_D k a ha r c hr hc hpres h
    have t1 : (if c + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by simp [h]
    have t2 : (if 0 < c then (if valAt a (r * (2 * k) + (c - 1)) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by
      by_cases hcp : 0 < c
      · simp [hcp, nbr_left_ne3 k a ha r c hr hc hcp (by omega)]
      · simp [hcp]
    have t3 : (if r + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 1 := by simp [hD.1, h]
    have t4 : (if 0 < r then (if valAt a ((r - 1) * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by
      by_cases hrp : 0 < r
      · simp [hrp, nbr_up_ne1 k a ha r c hr hc hrp (by omega)]
      · simp [hrp]
    linarith [t1, t2, t3, t4]
  · -- L : points left
    have hL := orient_L k a ha r c hr hc hpres h
    have t1 : (if c + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by simp [h]
    have t2 : (if 0 < c then (if valAt a (r * (2 * k) + (c - 1)) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 1 := by simp [hL.1, hL.2.2]
    have t3 : (if r + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by simp [h]
    have t4 : (if 0 < r then (if valAt a ((r - 1) * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by
      by_cases hrp : 0 < r
      · simp [hrp, nbr_up_ne1 k a ha r c hr hc hrp (by omega)]
      · simp [hrp]
    linarith [t1, t2, t3, t4]
  · -- R : points right
    have hR := orient_R k a ha r c hr hc hpres h
    have t1 : (if c + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 1 := by simp [hR.1, h]
    have t2 : (if 0 < c then (if valAt a (r * (2 * k) + (c - 1)) = (4 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by
      by_cases hcp : 0 < c
      · simp [hcp, nbr_left_ne3 k a ha r c hr hc hcp (by omega)]
      · simp [hcp]
    have t3 : (if r + 1 < 2 * k then (if valAt a (r * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by simp [h]
    have t4 : (if 0 < r then (if valAt a ((r - 1) * (2 * k) + c) = (2 : ℤ) then (1 : ℤ) else 0)
        else 0) = 0 := by
      by_cases hrp : 0 < r
      · simp [hrp, nbr_up_ne1 k a ha r c hr hc hrp (by omega)]
      · simp [hrp]
    linarith [t1, t2, t3, t4]

private lemma ite01 (P : Prop) [Decidable P] :
    (if P then (1 : ℤ) else 0) = 0 ∨ (if P then (1 : ℤ) else 0) = 1 := by
  by_cases h : P <;> simp [h]

/-- Two `0/1` indicators are equal iff their conditions are equivalent. -/
private lemma ite_eq_ite_iff {X Y : Prop} [Decidable X] [Decidable Y]
    (h : (if X then (1 : ℤ) else 0) = if Y then (1 : ℤ) else 0) : X ↔ Y := by
  by_cases hX : X <;> by_cases hY : Y <;> simp_all

/-- `piMap k a` is `{0,1}`-valued. -/
private lemma piMap_val01 (k : ℕ) (a : IntAssignment (2 * k * (2 * k))) (e : ℕ) :
    valAt (piMap k a) e = 0 ∨ valAt (piMap k a) e = 1 := by
  unfold valAt
  split_ifs with he
  · simp only [piMap]
    split_ifs <;> first | exact ite01 _ | (left; rfl)
  · left; rfl

/-- A *dead* edge (touching a removed corner) is never selected: `piMap k a` is `0` on
    it, because the orientation legality (`ne_const`) forbids pointing at a removed corner. -/
private lemma piMap_dead_zero (k : ℕ) (hk : 2 ≤ k) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (x : ℕ) (hx : x < 2 * (2 * k) * (2 * k - 1))
    (hdead : Bench.mutDead k x = true) :
    valAt (piMap k a) x = 0 := by
  have hN1 : 0 < 2 * k - 1 := by omega
  have hNpos : 0 < 2 * k := by omega
  have hPP : 2 * (2 * k) * (2 * k - 1) = (2 * k) * (2 * k - 1) + (2 * k) * (2 * k - 1) := by ring
  by_cases hxh : x < (2 * k) * (2 * k - 1)
  · -- horizontal edge h(r,c)
    set r := x / (2 * k - 1) with hr_def
    set c := x % (2 * k - 1) with hc_def
    have hclt : c < 2 * k - 1 := Nat.mod_lt _ hN1
    have hrlt : r < 2 * k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hxh)
    have hxrc : r * (2 * k - 1) + c = x := by
      rw [hr_def, hc_def, Nat.mul_comm]; exact Nat.div_add_mod x (2 * k - 1)
    have hmd : Bench.mutRemoved (2 * k) r c = true ∨ Bench.mutRemoved (2 * k) r (c + 1) = true := by
      have he : Bench.mutDead k x
          = (Bench.mutRemoved (2 * k) r c || Bench.mutRemoved (2 * k) r (c + 1)) := by
        simp only [Bench.mutDead]; rw [if_pos hxh, ← hr_def, ← hc_def]
      rw [he] at hdead; exact (Bool.or_eq_true _ _).mp hdead
    have hkey : valAt a (r * (2 * k) + c) ≠ 4 := by
      intro h3
      by_cases hpc : Bench.mutRemoved (2 * k) r c = false
      · have hrr := orient_R k a ha r c hrlt (by omega) hpc h3
        rcases hmd with h | h
        · rw [hpc] at h; simp at h
        · rw [hrr.2.1] at h; simp at h
      · have hrem : Bench.mutRemoved (2 * k) r c = true := by
          cases hb : Bench.mutRemoved (2 * k) r c with
          | false => exact absurd hb hpc
          | true => rfl
        rw [orient_removed_zero k a ha r c hrlt (by omega) hrem] at h3; omega
    rw [← hxrc, valAt_piMap_h k hk a r c hrlt (by omega), if_neg hkey]
  · -- vertical edge v(r,c)
    have hge : (2 * k) * (2 * k - 1) ≤ x := by omega
    set r := (x - (2 * k) * (2 * k - 1)) / (2 * k) with hr_def
    set c := (x - (2 * k) * (2 * k - 1)) % (2 * k) with hc_def
    have hclt : c < 2 * k := Nat.mod_lt _ hNpos
    have hylt : x - (2 * k) * (2 * k - 1) < (2 * k) * (2 * k - 1) := by omega
    have hrlt : r < 2 * k - 1 := Nat.div_lt_of_lt_mul hylt
    have hxrc : (2 * k) * (2 * k - 1) + r * (2 * k) + c = x := by
      have hsub : (2 * k) * r + c = x - (2 * k) * (2 * k - 1) := by
        rw [hr_def, hc_def]; exact Nat.div_add_mod _ (2 * k)
      have hcomm : r * (2 * k) = (2 * k) * r := Nat.mul_comm _ _
      omega
    have hmd : Bench.mutRemoved (2 * k) r c = true ∨ Bench.mutRemoved (2 * k) (r + 1) c = true := by
      have he : Bench.mutDead k x
          = (Bench.mutRemoved (2 * k) r c || Bench.mutRemoved (2 * k) (r + 1) c) := by
        simp only [Bench.mutDead]; rw [if_neg hxh, ← hr_def, ← hc_def]
      rw [he] at hdead; exact (Bool.or_eq_true _ _).mp hdead
    have hkey : valAt a (r * (2 * k) + c) ≠ 2 := by
      intro h1
      by_cases hpc : Bench.mutRemoved (2 * k) r c = false
      · have hdd := orient_D k a ha r c (by omega) hclt hpc h1
        rcases hmd with h | h
        · rw [hpc] at h; simp at h
        · rw [hdd.2.1] at h; simp at h
      · have hrem : Bench.mutRemoved (2 * k) r c = true := by
          cases hb : Bench.mutRemoved (2 * k) r c with
          | false => exact absurd hb hpc
          | true => rfl
        rw [orient_removed_zero k a ha r c (by omega) hclt hrem] at h1; omega
    rw [← hxrc, valAt_piMap_v k hk a r c (by omega) hclt, if_neg hkey]

/-- `gen_mutilated`'s constraints, with the `let`s unfolded. -/
private lemma mutilated_constraints_def (k : ℕ) :
    (gen_mutilated k).constraints =
      ((List.range (2 * (2 * k) * (2 * k - 1))).map
        (fun x => IntConstraint.bound x 0 (if Bench.mutDead k x then 0 else 1)))
      ++ ((List.range (2 * k)).flatMap fun r => (List.range (2 * k)).filterMap fun c =>
          if Bench.mutRemoved (2 * k) r c then none
          else some (IntConstraint.exactly_k (Bench.mutIncident k r c) 1)) := rfl

/-! ### The three π-equivalence obligations -/

/-- **Forward.** Every orientation solution projects to a matching solution. -/
theorem orient_forward (k : ℕ) (hk : 2 ≤ k) (a : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) :
    isSolutionInt (gen_mutilated k) (piMap k a) := by
  intro cstr hcstr
  rw [mutilated_constraints_def] at hcstr
  rcases List.mem_append.mp hcstr with hb | hcell
  · -- edge bound constraint
    obtain ⟨x, hxr, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hxr
    simp only [satisfiesConstraintInt, patternHolds]
    refine ⟨?_, ?_⟩
    · show (0 : ℤ) ≤ valAt (piMap k a) x
      rcases piMap_val01 k a x with h | h <;> omega
    · by_cases hd : Bench.mutDead k x = true
      · rw [if_pos hd]
        exact le_of_eq (piMap_dead_zero k hk a ha x hxr hd)
      · have hd' : Bench.mutDead k x = false := by
          cases hb2 : Bench.mutDead k x with
          | false => rfl
          | true => exact absurd hb2 hd
        rw [if_neg (by simp [hd'])]
        show valAt (piMap k a) x ≤ (1 : ℤ)
        rcases piMap_val01 k a x with h | h <;> omega
  · -- exact-cover constraint for a present cell
    obtain ⟨r, hrr, hrest⟩ := List.mem_flatMap.mp hcell
    obtain ⟨c, hcr, hfm⟩ := List.mem_filterMap.mp hrest
    rw [List.mem_range] at hrr hcr
    by_cases hh : Bench.mutRemoved (2 * k) r c = true
    · rw [if_pos hh] at hfm; exact absurd hfm (by simp)
    · have hpres : Bench.mutRemoved (2 * k) r c = false := by
        cases hb2 : Bench.mutRemoved (2 * k) r c with
        | false => rfl
        | true => exact absurd hb2 hh
      rw [if_neg hh, Option.some_inj] at hfm
      rw [← hfm]
      simp only [satisfiesConstraintInt, patternHolds]
      exact forward_cell k hk a ha r c hrr hcr hpres

private lemma edgeVal_eq_valAt (k : ℕ) (x : IntAssignment (2 * (2 * k) * (2 * k - 1))) (i : ℕ) :
    edgeVal k x i = valAt x i := rfl

/-- Each edge's bound under a matching solution. -/
private lemma x_edge_bound (k : ℕ) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) (e : ℕ) (he : e < 2 * (2 * k) * (2 * k - 1)) :
    0 ≤ valAt x e ∧ valAt x e ≤ (if Bench.mutDead k e then (0 : ℤ) else 1) := by
  have hmem : IntConstraint.bound e 0 (if Bench.mutDead k e then 0 else 1)
      ∈ (gen_mutilated k).constraints := by
    rw [mutilated_constraints_def]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨e, List.mem_range.mpr he, rfl⟩)
  have := hx _ hmem
  simpa only [satisfiesConstraintInt, patternHolds] using this

private lemma x_edge01 (k : ℕ) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) (e : ℕ) (he : e < 2 * (2 * k) * (2 * k - 1)) :
    valAt x e = 0 ∨ valAt x e = 1 := by
  obtain ⟨h0, h1⟩ := x_edge_bound k x hx e he
  have : valAt x e ≤ 1 := by split_ifs at h1 <;> omega
  omega

private lemma x_dead_zero (k : ℕ) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) (e : ℕ) (he : e < 2 * (2 * k) * (2 * k - 1))
    (hdead : Bench.mutDead k e = true) : valAt x e = 0 := by
  obtain ⟨h0, h1⟩ := x_edge_bound k x hx e he
  rw [if_pos hdead] at h1; omega

private lemma x_cell_sum (k : ℕ) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) :
    ((Bench.mutIncident k r c).map (valAt x)).sum = (1 : ℤ) := by
  have hmem : IntConstraint.exactly_k (Bench.mutIncident k r c) 1 ∈ (gen_mutilated k).constraints := by
    rw [mutilated_constraints_def]
    refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨r, List.mem_range.mpr hr, ?_⟩)
    refine List.mem_filterMap.mpr ⟨c, List.mem_range.mpr hc, ?_⟩
    rw [if_neg (by simp [hpres])]
  have := hx _ hmem
  simpa only [satisfiesConstraintInt, patternHolds] using this

/-- `liftOrient k x` evaluated at the cell index `(r,c)`, with the index arithmetic resolved. -/
private lemma lift_at (k : ℕ) (hk : 2 ≤ k) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k) :
    valAt (liftOrient k x) (r * (2 * k) + c) =
      (if Bench.mutRemoved (2 * k) r c then 0
       else if decide (c + 1 < 2 * k) && (valAt x (r * (2 * k - 1) + c) == 1) then 4
       else if decide (0 < c) && (valAt x (r * (2 * k - 1) + (c - 1)) == 1) then 3
       else if decide (r + 1 < 2 * k) && (valAt x (2 * k * (2 * k - 1) + r * (2 * k) + c) == 1) then 2
       else if decide (0 < r) && (valAt x (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) == 1) then 1
       else 0) := by
  have hcell : r * (2 * k) + c < 2 * k * (2 * k) := by
    have h1 : (r + 1) * (2 * k) ≤ (2 * k) * (2 * k) := Nat.mul_le_mul_right _ (by omega)
    have h2 : r * (2 * k) + (2 * k) = (r + 1) * (2 * k) := by ring
    omega
  have hdiv : (r * (2 * k) + c) / (2 * k) = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (show 0 < 2 * k by omega),
        Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (r * (2 * k) + c) % (2 * k) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hval : valAt (liftOrient k x) (r * (2 * k) + c) = liftOrient k x ⟨r * (2 * k) + c, hcell⟩ := by
    unfold valAt; rw [dif_pos hcell]
  rw [hval]
  simp only [liftOrient, edgeVal_eq_valAt, hdiv, hmod]

/-- Decomposed incident-edge sum for `x` at a present cell (mirrors `forward_cell`). -/
private lemma x_sum_decomp (k : ℕ) (_hk : 2 ≤ k) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) :
    (if c + 1 < 2 * k then valAt x (r * (2 * k - 1) + c) else 0)
    + (if 0 < c then valAt x (r * (2 * k - 1) + (c - 1)) else 0)
    + (if r + 1 < 2 * k then valAt x (2 * k * (2 * k - 1) + r * (2 * k) + c) else 0)
    + (if 0 < r then valAt x (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) else 0) = 1 := by
  have hcond : ∀ (P : Prop) [Decidable P] (e : ℕ),
      (List.map (valAt x) (if P then [e] else [])).sum = if P then valAt x e else 0 := by
    intro P _ e; split_ifs <;> simp
  have h := x_cell_sum k x hx r c hr hc hpres
  simp only [Bench.mutIncident, List.map_append, List.sum_append, hcond] at h
  exact h

/-- An incident-edge index is in range. -/
private lemma h_edge_lt (k r c : ℕ) (hk : 2 ≤ k) (hr : r < 2 * k) (hc : c + 1 < 2 * k) :
    r * (2 * k - 1) + c < 2 * (2 * k) * (2 * k - 1) := by
  have h1 : (r + 1) * (2 * k - 1) ≤ (2 * k) * (2 * k - 1) := Nat.mul_le_mul_right _ (by omega)
  have h2 : r * (2 * k - 1) + (2 * k - 1) = (r + 1) * (2 * k - 1) := by ring
  have h3 : (2 * k) * (2 * k - 1) ≤ 2 * (2 * k) * (2 * k - 1) := by nlinarith
  omega

private lemma v_edge_lt (k r c : ℕ) (hk : 2 ≤ k) (hr : r + 1 < 2 * k) (hc : c < 2 * k) :
    2 * k * (2 * k - 1) + r * (2 * k) + c < 2 * (2 * k) * (2 * k - 1) := by
  have hcellH : r * (2 * k) + c < (2 * k) * (2 * k - 1) := by
    have h1 : (r + 1) * (2 * k) ≤ (2 * k - 1) * (2 * k) := Nat.mul_le_mul_right _ (by omega)
    have h2 : r * (2 * k) + (2 * k) = (r + 1) * (2 * k) := by ring
    have h3 : (2 * k - 1) * (2 * k) = (2 * k) * (2 * k - 1) := by ring
    omega
  have h4 : 2 * (2 * k) * (2 * k - 1) = (2 * k) * (2 * k - 1) + (2 * k) * (2 * k - 1) := by ring
  omega

/-- A horizontal edge incident to a removed corner is dead. -/
private lemma h_edge_dead_of (k r c : ℕ) (hk : 2 ≤ k) (hr : r < 2 * k) (hc : c + 1 < 2 * k)
    (hrem : Bench.mutRemoved (2 * k) r c = true ∨ Bench.mutRemoved (2 * k) r (c + 1) = true) :
    Bench.mutDead k (r * (2 * k - 1) + c) = true := by
  have hN1 : 0 < 2 * k - 1 := by omega
  have hcN1 : c < 2 * k - 1 := by omega
  have hnH : r * (2 * k - 1) + c < (2 * k) * (2 * k - 1) := by
    have h1 : (r + 1) * (2 * k - 1) ≤ (2 * k) * (2 * k - 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : r * (2 * k - 1) + (2 * k - 1) = (r + 1) * (2 * k - 1) := by ring
    omega
  have hdiv : (r * (2 * k - 1) + c) / (2 * k - 1) = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN1, Nat.div_eq_of_lt hcN1, Nat.zero_add]
  have hmod : (r * (2 * k - 1) + c) % (2 * k - 1) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcN1]
  simp only [Bench.mutDead]
  rw [if_pos hnH, hdiv, hmod]
  rcases hrem with h | h <;> simp [h]

/-- A vertical edge incident to a removed corner is dead. -/
private lemma v_edge_dead_of (k r c : ℕ) (hk : 2 ≤ k) (_hr : r + 1 < 2 * k) (hc : c < 2 * k)
    (hrem : Bench.mutRemoved (2 * k) r c = true ∨ Bench.mutRemoved (2 * k) (r + 1) c = true) :
    Bench.mutDead k (2 * k * (2 * k - 1) + r * (2 * k) + c) = true := by
  have hNpos : 0 < 2 * k := by omega
  have hge : ¬ (2 * k * (2 * k - 1) + r * (2 * k) + c < (2 * k) * (2 * k - 1)) := by omega
  have hsub : 2 * k * (2 * k - 1) + r * (2 * k) + c - (2 * k) * (2 * k - 1) = r * (2 * k) + c := by
    omega
  have hdiv : (r * (2 * k) + c) / (2 * k) = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hNpos, Nat.div_eq_of_lt hc, Nat.zero_add]
  have hmod : (r * (2 * k) + c) % (2 * k) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  simp only [Bench.mutDead]
  rw [if_neg hge, hsub, hdiv, hmod]
  rcases hrem with h | h <;> simp [h]

/-- **The lift direction.** For a present cell, `liftOrient` returns the direction of the
    unique selected incident edge. -/
private lemma lift_cases (k : ℕ) (hk : 2 ≤ k) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) :
    (valAt (liftOrient k x) (r * (2 * k) + c) = 4 ∧ c + 1 < 2 * k
        ∧ valAt x (r * (2 * k - 1) + c) = 1) ∨
    (valAt (liftOrient k x) (r * (2 * k) + c) = 3 ∧ 0 < c
        ∧ valAt x (r * (2 * k - 1) + (c - 1)) = 1) ∨
    (valAt (liftOrient k x) (r * (2 * k) + c) = 2 ∧ r + 1 < 2 * k
        ∧ valAt x (2 * k * (2 * k - 1) + r * (2 * k) + c) = 1) ∨
    (valAt (liftOrient k x) (r * (2 * k) + c) = 1 ∧ 0 < r
        ∧ valAt x (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) = 1) := by
  rw [lift_at k hk x r c hr hc, if_neg (by simp [hpres])]
  split_ifs with hR hL hD hU
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hR
    exact Or.inl ⟨rfl, hR.1, hR.2⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hL
    exact Or.inr (Or.inl ⟨rfl, hL.1, hL.2⟩)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hD
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hD.1, hD.2⟩))
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hU
    exact Or.inr (Or.inr (Or.inr ⟨rfl, hU.1, hU.2⟩))
  · exfalso
    have hsum := x_sum_decomp k hk x hx r c hr hc hpres
    have heR : (if c + 1 < 2 * k then valAt x (r * (2 * k - 1) + c) else 0) = 0 := by
      by_cases hg : c + 1 < 2 * k
      · rw [if_pos hg]
        rcases x_edge01 k x hx _ (h_edge_lt k r c hk hr hg) with h | h
        · exact h
        · exact absurd (by simp [hg, h]) hR
      · rw [if_neg hg]
    have heL : (if 0 < c then valAt x (r * (2 * k - 1) + (c - 1)) else 0) = 0 := by
      by_cases hg : 0 < c
      · rw [if_pos hg]
        rcases x_edge01 k x hx _ (h_edge_lt k r (c - 1) hk hr (by omega)) with h | h
        · exact h
        · exact absurd (by simp [hg, h]) hL
      · rw [if_neg hg]
    have heD : (if r + 1 < 2 * k then valAt x (2 * k * (2 * k - 1) + r * (2 * k) + c) else 0) = 0 := by
      by_cases hg : r + 1 < 2 * k
      · rw [if_pos hg]
        rcases x_edge01 k x hx _ (v_edge_lt k r c hk hg hc) with h | h
        · exact h
        · exact absurd (by simp [hg, h]) hD
      · rw [if_neg hg]
    have heU : (if 0 < r then valAt x (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) else 0) = 0 := by
      by_cases hg : 0 < r
      · rw [if_pos hg]
        rcases x_edge01 k x hx _ (v_edge_lt k (r - 1) c hk (by omega) hc) with h | h
        · exact h
        · exact absurd (by simp [hg, h]) hU
      · rw [if_neg hg]
    rw [heR, heL, heD, heU] at hsum
    omega

/-- **Direction ⟺ selected edge.** For a present cell, `liftOrient` points `d` iff `d`'s
    incident edge is the (unique) selected one. -/
private lemma lift_iff (k : ℕ) (hk : 2 ≤ k) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) :
    (valAt (liftOrient k x) (r * (2 * k) + c) = 4 ↔ c + 1 < 2 * k ∧ valAt x (r * (2 * k - 1) + c) = 1) ∧
    (valAt (liftOrient k x) (r * (2 * k) + c) = 3 ↔ 0 < c ∧ valAt x (r * (2 * k - 1) + (c - 1)) = 1) ∧
    (valAt (liftOrient k x) (r * (2 * k) + c) = 2 ↔
        r + 1 < 2 * k ∧ valAt x (2 * k * (2 * k - 1) + r * (2 * k) + c) = 1) ∧
    (valAt (liftOrient k x) (r * (2 * k) + c) = 1 ↔
        0 < r ∧ valAt x (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) = 1) := by
  have hsum := x_sum_decomp k hk x hx r c hr hc hpres
  have p1 : 0 ≤ (if c + 1 < 2 * k then valAt x (r * (2 * k - 1) + c) else 0) := by
    by_cases hg : c + 1 < 2 * k
    · rw [if_pos hg]; exact (x_edge_bound k x hx _ (h_edge_lt k r c hk hr hg)).1
    · rw [if_neg hg]
  have p2 : 0 ≤ (if 0 < c then valAt x (r * (2 * k - 1) + (c - 1)) else 0) := by
    by_cases hg : 0 < c
    · rw [if_pos hg]; exact (x_edge_bound k x hx _ (h_edge_lt k r (c - 1) hk hr (by omega))).1
    · rw [if_neg hg]
  have p3 : 0 ≤ (if r + 1 < 2 * k then valAt x (2 * k * (2 * k - 1) + r * (2 * k) + c) else 0) := by
    by_cases hg : r + 1 < 2 * k
    · rw [if_pos hg]; exact (x_edge_bound k x hx _ (v_edge_lt k r c hk hg hc)).1
    · rw [if_neg hg]
  have p4 : 0 ≤ (if 0 < r then valAt x (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) else 0) := by
    by_cases hg : 0 < r
    · rw [if_pos hg]; exact (x_edge_bound k x hx _ (v_edge_lt k (r - 1) c hk (by omega) hc)).1
    · rw [if_neg hg]
  obtain lc := lift_cases k hk x hx r c hr hc hpres
  refine ⟨⟨fun h => ?_, fun ⟨hg, he⟩ => ?_⟩, ⟨fun h => ?_, fun ⟨hg, he⟩ => ?_⟩,
          ⟨fun h => ?_, fun ⟨hg, he⟩ => ?_⟩, ⟨fun h => ?_, fun ⟨hg, he⟩ => ?_⟩⟩
  · rcases lc with ⟨hv, hg, he⟩ | ⟨hv, _, _⟩ | ⟨hv, _, _⟩ | ⟨hv, _, _⟩
    exacts [⟨hg, he⟩, by omega, by omega, by omega]
  · rcases lc with ⟨hv, _, _⟩ | ⟨_, hg2, he2⟩ | ⟨_, hg2, he2⟩ | ⟨_, hg2, he2⟩
    · exact hv
    · exfalso; rw [if_pos hg, if_pos hg2, he, he2] at hsum; omega
    · exfalso; rw [if_pos hg, if_pos hg2, he, he2] at hsum; omega
    · exfalso; rw [if_pos hg, if_pos hg2, he, he2] at hsum; omega
  · rcases lc with ⟨hv, _, _⟩ | ⟨hv, hg, he⟩ | ⟨hv, _, _⟩ | ⟨hv, _, _⟩
    exacts [by omega, ⟨hg, he⟩, by omega, by omega]
  · rcases lc with ⟨_, hg2, he2⟩ | ⟨hv, _, _⟩ | ⟨_, hg2, he2⟩ | ⟨_, hg2, he2⟩
    · exfalso; rw [if_pos hg2, if_pos hg, he2, he] at hsum; omega
    · exact hv
    · exfalso; rw [if_pos hg, if_pos hg2, he, he2] at hsum; omega
    · exfalso; rw [if_pos hg, if_pos hg2, he, he2] at hsum; omega
  · rcases lc with ⟨hv, _, _⟩ | ⟨hv, _, _⟩ | ⟨hv, hg, he⟩ | ⟨hv, _, _⟩
    exacts [by omega, by omega, ⟨hg, he⟩, by omega]
  · rcases lc with ⟨_, hg2, he2⟩ | ⟨_, hg2, he2⟩ | ⟨hv, _, _⟩ | ⟨_, hg2, he2⟩
    · exfalso; rw [if_pos hg2, if_pos hg, he2, he] at hsum; omega
    · exfalso; rw [if_pos hg2, if_pos hg, he2, he] at hsum; omega
    · exact hv
    · exfalso; rw [if_pos hg, if_pos hg2, he, he2] at hsum; omega
  · rcases lc with ⟨hv, _, _⟩ | ⟨hv, _, _⟩ | ⟨hv, _, _⟩ | ⟨hv, hg, he⟩
    exacts [by omega, by omega, by omega, ⟨hg, he⟩]
  · rcases lc with ⟨_, hg2, he2⟩ | ⟨_, hg2, he2⟩ | ⟨_, hg2, he2⟩ | ⟨hv, _, _⟩
    · exfalso; rw [if_pos hg2, if_pos hg, he2, he] at hsum; omega
    · exfalso; rw [if_pos hg2, if_pos hg, he2, he] at hsum; omega
    · exfalso; rw [if_pos hg2, if_pos hg, he2, he] at hsum; omega
    · exact hv

private lemma lift_removed (k : ℕ) (hk : 2 ≤ k) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k) (hrem : Bench.mutRemoved (2 * k) r c = true) :
    valAt (liftOrient k x) (r * (2 * k) + c) = 0 := by
  rw [lift_at k hk x r c hr hc, if_pos hrem]

private lemma lift_range (k : ℕ) (hk : 2 ≤ k) (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x)
    (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k) (hpres : Bench.mutRemoved (2 * k) r c = false) :
    1 ≤ valAt (liftOrient k x) (r * (2 * k) + c)
      ∧ valAt (liftOrient k x) (r * (2 * k) + c) ≤ 4 := by
  rcases lift_cases k hk x hx r c hr hc hpres with ⟨hv, _, _⟩ | ⟨hv, _, _⟩ | ⟨hv, _, _⟩ | ⟨hv, _, _⟩ <;>
    rw [hv] <;> omega

/-- **Backward.** Every matching solution lifts to an orientation solution that
    projects back to it. -/
theorem orient_backward (k : ℕ) (hk : 2 ≤ k)
    (x : IntAssignment (2 * (2 * k) * (2 * k - 1)))
    (hx : isSolutionInt (gen_mutilated k) x) :
    isSolutionInt (gen_orient k) (liftOrient k x) ∧ piMap k (liftOrient k x) = x := by
  constructor
  · -- `liftOrient k x` is a `gen_orient` solution
    intro cstr hcstr
    rw [orient_constraints_def] at hcstr
    rcases List.mem_append.mp hcstr with hb | hrec
    · -- bound constraint
      obtain ⟨r, hrr, hrest⟩ := List.mem_flatMap.mp hb
      obtain ⟨c, hcr, heq⟩ := List.mem_map.mp hrest
      rw [List.mem_range] at hrr hcr
      by_cases hrem : Bench.mutRemoved (2 * k) r c = true
      · rw [if_pos hrem] at heq; subst heq
        simp only [satisfiesConstraintInt, patternHolds]
        have hz := lift_removed k hk x r c hrr hcr hrem
        exact ⟨le_of_eq hz.symm, le_of_eq hz⟩
      · have hpres : Bench.mutRemoved (2 * k) r c = false := by
          cases hb2 : Bench.mutRemoved (2 * k) r c with
          | false => rfl
          | true => exact absurd hb2 hrem
        rw [if_neg (by simp [hpres])] at heq; subst heq
        simp only [satisfiesConstraintInt, patternHolds]
        exact lift_range k hk x hx r c hrr hcr hpres
    · -- reciprocity / legality constraint
      obtain ⟨r, hrr, hrest⟩ := List.mem_flatMap.mp hrec
      obtain ⟨c, hcr, hrest2⟩ := List.mem_flatMap.mp hrest
      rw [List.mem_range] at hrr hcr
      by_cases hrem : Bench.mutRemoved (2 * k) r c = true
      · rw [if_pos hrem] at hrest2; cases hrest2
      · have hpres : Bench.mutRemoved (2 * k) r c = false := by
          cases hb2 : Bench.mutRemoved (2 * k) r c with
          | false => rfl
          | true => exact absurd hb2 hrem
        rw [if_neg hrem] at hrest2
        obtain ⟨iff3, iff2, iff1, iff0⟩ := lift_iff k hk x hx r c hrr hcr hpres
        rcases List.mem_append.mp hrest2 with hbl | hU
        rcases List.mem_append.mp hbl with hbl2 | hD
        rcases List.mem_append.mp hbl2 with hR | hL
        · -- R block
          split_ifs at hR with hl
          · obtain rfl := List.eq_of_mem_singleton hR
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
            simp only [satisfiesConstraintInt, patternHolds]
            by_cases h3 : valAt (liftOrient k x) (r * (2 * k) + c) = 4
            · right
              have : valAt x (r * (2 * k - 1) + c) = 1 := (iff3.mp h3).2
              obtain ⟨_, iff2', _, _⟩ := lift_iff k hk x hx r (c + 1) hrr (by omega) hl.2
              exact iff2'.mpr ⟨by omega, by rw [show c + 1 - 1 = c from by omega]; exact this⟩
            · left; exact h3
          · obtain rfl := List.eq_of_mem_singleton hR
            simp only [satisfiesConstraintInt, patternHolds]
            intro h3
            obtain ⟨hc1, hon⟩ := iff3.mp h3
            have hnd := h_edge_dead_of k r c hk hrr hc1
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
              not_and] at hl
            have hrem' : Bench.mutRemoved (2 * k) r (c + 1) = true := by
              cases hb2 : Bench.mutRemoved (2 * k) r (c + 1) with
              | false => exact absurd (hl hc1) (by simp [hb2])
              | true => rfl
            rw [x_dead_zero k x hx _ (h_edge_lt k r c hk hrr hc1) (hnd (Or.inr hrem'))] at hon
            omega
        · -- L block
          split_ifs at hL with hl
          · obtain rfl := List.eq_of_mem_singleton hL
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
            simp only [satisfiesConstraintInt, patternHolds]
            by_cases h2 : valAt (liftOrient k x) (r * (2 * k) + c) = 3
            · right
              have hon : valAt x (r * (2 * k - 1) + (c - 1)) = 1 := (iff2.mp h2).2
              obtain ⟨iff3', _, _, _⟩ := lift_iff k hk x hx r (c - 1) hrr (by omega) hl.2
              exact iff3'.mpr ⟨by omega, hon⟩
            · left; exact h2
          · obtain rfl := List.eq_of_mem_singleton hL
            simp only [satisfiesConstraintInt, patternHolds]
            intro h2
            obtain ⟨hc0, hon⟩ := iff2.mp h2
            have hnd := h_edge_dead_of k r (c - 1) hk hrr (by omega)
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
              not_and] at hl
            have hrem' : Bench.mutRemoved (2 * k) r (c - 1) = true := by
              cases hb2 : Bench.mutRemoved (2 * k) r (c - 1) with
              | false => exact absurd (hl hc0) (by simp [hb2])
              | true => rfl
            rw [x_dead_zero k x hx _ (h_edge_lt k r (c - 1) hk hrr (by omega)) (hnd (Or.inl hrem'))] at hon
            omega
        · -- D block
          split_ifs at hD with hl
          · obtain rfl := List.eq_of_mem_singleton hD
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
            simp only [satisfiesConstraintInt, patternHolds]
            by_cases h1 : valAt (liftOrient k x) (r * (2 * k) + c) = 2
            · right
              have hon : valAt x (2 * k * (2 * k - 1) + r * (2 * k) + c) = 1 := (iff1.mp h1).2
              obtain ⟨_, _, _, iff0'⟩ := lift_iff k hk x hx (r + 1) c (by omega) hcr hl.2
              exact iff0'.mpr ⟨by omega, by rw [show r + 1 - 1 = r from by omega]; exact hon⟩
            · left; exact h1
          · obtain rfl := List.eq_of_mem_singleton hD
            simp only [satisfiesConstraintInt, patternHolds]
            intro h1
            obtain ⟨hr1, hon⟩ := iff1.mp h1
            have hnd := v_edge_dead_of k r c hk hr1 hcr
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
              not_and] at hl
            have hrem' : Bench.mutRemoved (2 * k) (r + 1) c = true := by
              cases hb2 : Bench.mutRemoved (2 * k) (r + 1) c with
              | false => exact absurd (hl hr1) (by simp [hb2])
              | true => rfl
            rw [x_dead_zero k x hx _ (v_edge_lt k r c hk hr1 hcr) (hnd (Or.inr hrem'))] at hon
            omega
        · -- U block
          split_ifs at hU with hl
          · obtain rfl := List.eq_of_mem_singleton hU
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hl
            simp only [satisfiesConstraintInt, patternHolds]
            by_cases h0 : valAt (liftOrient k x) (r * (2 * k) + c) = 1
            · right
              have hon : valAt x (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c) = 1 := (iff0.mp h0).2
              obtain ⟨_, _, iff1', _⟩ := lift_iff k hk x hx (r - 1) c (by omega) hcr hl.2
              exact iff1'.mpr ⟨by omega, hon⟩
            · left; exact h0
          · obtain rfl := List.eq_of_mem_singleton hU
            simp only [satisfiesConstraintInt, patternHolds]
            intro h0
            obtain ⟨hr0, hon⟩ := iff0.mp h0
            have hnd := v_edge_dead_of k (r - 1) c hk (by omega) hcr
            simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
              not_and] at hl
            have hrem' : Bench.mutRemoved (2 * k) (r - 1) c = true := by
              cases hb2 : Bench.mutRemoved (2 * k) (r - 1) c with
              | false => exact absurd (hl hr0) (by simp [hb2])
              | true => rfl
            rw [x_dead_zero k x hx _ (v_edge_lt k (r - 1) c hk (by omega) hcr) (hnd (Or.inl hrem'))] at hon
            omega
  · -- `piMap k (liftOrient k x) = x`
    have hkey : ∀ i, i < 2 * (2 * k) * (2 * k - 1) →
        valAt (piMap k (liftOrient k x)) i = valAt x i := by
      intro i hi
      have hN1 : 0 < 2 * k - 1 := by omega
      have hNpos : 0 < 2 * k := by omega
      by_cases hih : i < (2 * k) * (2 * k - 1)
      · -- horizontal edge
        have hc : i % (2 * k - 1) < 2 * k - 1 := Nat.mod_lt _ hN1
        have hr : i / (2 * k - 1) < 2 * k := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hih)
        have hirc : i / (2 * k - 1) * (2 * k - 1) + i % (2 * k - 1) = i := by
          rw [Nat.mul_comm]; exact Nat.div_add_mod i (2 * k - 1)
        set r := i / (2 * k - 1)
        set c := i % (2 * k - 1)
        rw [← hirc, valAt_piMap_h k hk (liftOrient k x) r c hr (by omega)]
        by_cases hrem : Bench.mutRemoved (2 * k) r c = true
        · rw [lift_removed k hk x r c hr (by omega) hrem,
              x_dead_zero k x hx _ (h_edge_lt k r c hk hr (by omega))
                (h_edge_dead_of k r c hk hr (by omega) (Or.inl hrem))]
          norm_num
        · have hpres : Bench.mutRemoved (2 * k) r c = false := by
            cases hb2 : Bench.mutRemoved (2 * k) r c with
            | false => rfl
            | true => exact absurd hb2 hrem
          obtain ⟨iff3, _, _, _⟩ := lift_iff k hk x hx r c hr (by omega) hpres
          rcases x_edge01 k x hx _ (h_edge_lt k r c hk hr (by omega)) with h | h
          · rw [h]; rw [if_neg (by rw [iff3]; rintro ⟨_, h1⟩; rw [h] at h1; exact absurd h1 (by norm_num))]
          · rw [h]; rw [if_pos (iff3.mpr ⟨by omega, h⟩)]
      · -- vertical edge
        have hge : (2 * k) * (2 * k - 1) ≤ i := by omega
        have hc : (i - (2 * k) * (2 * k - 1)) % (2 * k) < 2 * k := Nat.mod_lt _ hNpos
        have hylt : i - (2 * k) * (2 * k - 1) < (2 * k) * (2 * k - 1) := by
          have hPP : 2 * (2 * k) * (2 * k - 1) = (2 * k) * (2 * k - 1) + (2 * k) * (2 * k - 1) := by
            ring
          omega
        have hr : (i - (2 * k) * (2 * k - 1)) / (2 * k) < 2 * k - 1 := Nat.div_lt_of_lt_mul hylt
        have hirc : (2 * k) * (2 * k - 1)
            + (i - (2 * k) * (2 * k - 1)) / (2 * k) * (2 * k) + (i - (2 * k) * (2 * k - 1)) % (2 * k) = i := by
          have hsub : (2 * k) * ((i - (2 * k) * (2 * k - 1)) / (2 * k))
              + (i - (2 * k) * (2 * k - 1)) % (2 * k) = i - (2 * k) * (2 * k - 1) := Nat.div_add_mod _ (2 * k)
          have hcomm : (i - (2 * k) * (2 * k - 1)) / (2 * k) * (2 * k)
              = (2 * k) * ((i - (2 * k) * (2 * k - 1)) / (2 * k)) := Nat.mul_comm _ _
          omega
        set r := (i - (2 * k) * (2 * k - 1)) / (2 * k)
        set c := (i - (2 * k) * (2 * k - 1)) % (2 * k)
        rw [← hirc, valAt_piMap_v k hk (liftOrient k x) r c (by omega) hc]
        by_cases hrem : Bench.mutRemoved (2 * k) r c = true
        · rw [lift_removed k hk x r c (by omega) hc hrem,
              x_dead_zero k x hx _ (v_edge_lt k r c hk (by omega) hc)
                (v_edge_dead_of k r c hk (by omega) hc (Or.inl hrem))]
          norm_num
        · have hpres : Bench.mutRemoved (2 * k) r c = false := by
            cases hb2 : Bench.mutRemoved (2 * k) r c with
            | false => rfl
            | true => exact absurd hb2 hrem
          obtain ⟨_, _, iff1, _⟩ := lift_iff k hk x hx r c (by omega) hc hpres
          rcases x_edge01 k x hx _ (v_edge_lt k r c hk (by omega) hc) with h | h
          · rw [h]; rw [if_neg (by rw [iff1]; rintro ⟨_, h1⟩; rw [h] at h1; exact absurd h1 (by norm_num))]
          · rw [h]; rw [if_pos (iff1.mpr ⟨by omega, h⟩)]
    funext e
    have h := hkey e.val e.isLt
    rwa [show valAt (piMap k (liftOrient k x)) e.val = piMap k (liftOrient k x) e from by
          unfold valAt; rw [dif_pos e.isLt],
         show valAt x e.val = x e from by unfold valAt; rw [dif_pos e.isLt]] at h

/-- **Per-cell recovery.** Two orientation solutions with the same projection agree on
    every present cell: the cell's direction is determined by which incident edge of
    `piMap` is selected. -/
private lemma orient_recover (k : ℕ) (hk : 2 ≤ k) (a a' : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (ha' : isSolutionInt (gen_orient k) a')
    (hpi : piMap k a = piMap k a') (r c : ℕ) (hr : r < 2 * k) (hc : c < 2 * k)
    (hpres : Bench.mutRemoved (2 * k) r c = false) :
    valAt a (r * (2 * k) + c) = valAt a' (r * (2 * k) + c) := by
  have hedge : ∀ e, valAt (piMap k a) e = valAt (piMap k a') e := fun e => by rw [hpi]
  obtain ⟨hge, hle⟩ := orient_range k a ha r c hr hc hpres
  rcases (show valAt a (r * (2 * k) + c) = 1 ∨ valAt a (r * (2 * k) + c) = 2
      ∨ valAt a (r * (2 * k) + c) = 3 ∨ valAt a (r * (2 * k) + c) = 4 from by omega)
    with h | h | h | h
  · -- U = 1: the up edge `v(r-1,c)` is selected
    have hU := orient_U k a ha r c hr hc hpres h
    have hiff : valAt a ((r - 1) * (2 * k) + c) = 2 ↔ valAt a' ((r - 1) * (2 * k) + c) = 2 := by
      apply ite_eq_ite_iff
      have he := hedge (2 * k * (2 * k - 1) + (r - 1) * (2 * k) + c)
      rwa [valAt_piMap_v k hk a (r - 1) c (by omega) hc,
           valAt_piMap_v k hk a' (r - 1) c (by omega) hc] at he
    have hD := orient_D k a' ha' (r - 1) c (by omega) hc hU.2.1 (hiff.mp hU.2.2)
    rw [show r - 1 + 1 = r from by omega] at hD
    have := hD.2.2; omega
  · -- D = 2: the down edge `v(r,c)` is selected
    have hD := orient_D k a ha r c hr hc hpres h
    have hiff : valAt a (r * (2 * k) + c) = 2 ↔ valAt a' (r * (2 * k) + c) = 2 := by
      apply ite_eq_ite_iff
      have he := hedge (2 * k * (2 * k - 1) + r * (2 * k) + c)
      rwa [valAt_piMap_v k hk a r c hD.1 hc, valAt_piMap_v k hk a' r c hD.1 hc] at he
    have := hiff.mp h; omega
  · -- L = 3: the left edge `h(r,c-1)` is selected
    have hL := orient_L k a ha r c hr hc hpres h
    have hiff : valAt a (r * (2 * k) + (c - 1)) = 4 ↔ valAt a' (r * (2 * k) + (c - 1)) = 4 := by
      apply ite_eq_ite_iff
      have he := hedge (r * (2 * k - 1) + (c - 1))
      rwa [valAt_piMap_h k hk a r (c - 1) hr (by omega),
           valAt_piMap_h k hk a' r (c - 1) hr (by omega)] at he
    have hR := orient_R k a' ha' r (c - 1) hr (by omega) hL.2.1 (hiff.mp hL.2.2)
    rw [show c - 1 + 1 = c from by omega] at hR
    have := hR.2.2; omega
  · -- R = 4: the right edge `h(r,c)` is selected
    have hR := orient_R k a ha r c hr hc hpres h
    have hiff : valAt a (r * (2 * k) + c) = 4 ↔ valAt a' (r * (2 * k) + c) = 4 := by
      apply ite_eq_ite_iff
      have he := hedge (r * (2 * k - 1) + c)
      rwa [valAt_piMap_h k hk a r c hr hR.1, valAt_piMap_h k hk a' r c hr hR.1] at he
    have := hiff.mp h; omega

/-- **Injectivity.** `π` is injective on orientation solutions. -/
theorem orient_injective (k : ℕ) (hk : 2 ≤ k) (a a' : IntAssignment (2 * k * (2 * k)))
    (ha : isSolutionInt (gen_orient k) a) (ha' : isSolutionInt (gen_orient k) a')
    (heq : piMap k a = piMap k a') : a = a' := by
  funext p
  obtain ⟨i, hi⟩ := p
  have hval : ∀ b : IntAssignment (2 * k * (2 * k)), b ⟨i, hi⟩ = valAt b i := by
    intro b; unfold valAt; rw [dif_pos hi]
  rw [hval a, hval a']
  have hc2 : i % (2 * k) < 2 * k := Nat.mod_lt _ (by omega)
  have hr2 : i / (2 * k) < 2 * k := Nat.div_lt_of_lt_mul hi
  have hirc : i / (2 * k) * (2 * k) + i % (2 * k) = i := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod i (2 * k)
  rw [← hirc]
  by_cases hrem : Bench.mutRemoved (2 * k) (i / (2 * k)) (i % (2 * k)) = true
  · rw [orient_removed_zero k a ha _ _ hr2 hc2 hrem,
        orient_removed_zero k a' ha' _ _ hr2 hc2 hrem]
  · have hpres : Bench.mutRemoved (2 * k) (i / (2 * k)) (i % (2 * k)) = false := by
      cases hb : Bench.mutRemoved (2 * k) (i / (2 * k)) (i % (2 * k)) with
      | false => rfl
      | true => exact absurd hb hrem
    exact orient_recover k hk a a' ha ha' heq _ _ hr2 hc2 hpres

/-! ### Assembly -/

/-- The orientation model is π-equivalent to the edge / exact-cover model. -/
theorem mutilated_orient_pi_equivalent (k : ℕ) (hk : 2 ≤ k) :
    piEquivalent (gen_mutilated k) (gen_orient k) (piMap k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sol₂ h
    exact orient_forward k hk sol₂ h
  · intro sol₁ h
    obtain ⟨hsol, hproj⟩ := orient_backward k hk sol₁ h
    exact ⟨liftOrient k sol₁, hsol, hproj⟩
  · intro sol₂ sol₂' h h' heq
    exact orient_injective k hk sol₂ sol₂' h h' heq

/-- **The main result.** The orientation and edge / exact-cover models are
    *equivalent* — there is a bijection between their solution sets — immediate
    from `mutilated_orient_pi_equivalent` via `piEquivalent_implies_equivalent`. -/
theorem mutilated_orient_equivalent (k : ℕ) (hk : 2 ≤ k) :
    equivalent (gen_orient k) (gen_mutilated k) :=
  piEquivalent_implies_equivalent _ _ _ (mutilated_orient_pi_equivalent k hk)

/-- Hence the two models are equisatisfiable. -/
theorem mutilated_orient_equisatisfiable (k : ℕ) (hk : 2 ≤ k) :
    equisatisfiable (gen_mutilated k) (gen_orient k) :=
  piEquivalent_implies_equisatisfiable _ _ _ (mutilated_orient_pi_equivalent k hk)

/-- UNSAT of the edge model transfers to the orientation model. -/
theorem mutilated_orient_unsat_of_edge_unsat (k : ℕ) (hk : 2 ≤ k)
    (h : ¬ (gen_mutilated k).isSatisfiableInt) :
    ¬ (gen_orient k).isSatisfiableInt :=
  fun hgo => h ((mutilated_orient_equisatisfiable k hk).mpr hgo)

end CSP.L2S.MutilatedOrient
