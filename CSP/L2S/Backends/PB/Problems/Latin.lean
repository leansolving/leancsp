import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«07_latin_squares»

namespace CSP.L2S.PB.Latin

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for a Latin square with contradictory givens

This extends the "givens / clues" family (opened by `Sudoku.lean`) to the
**binary-encoded** Latin square of `Tests/lean/07_latin_squares.lean`, and is the
**first `sum_eq` (unit-coefficient sum) consumer** of the PB pipeline.

The corpus `latin_square_csp n` encodes an `n×n` Latin square with `n³` Boolean
indicators `x[i,j,k] ∈ {0,1}` (`x[i,j,k] = 1` iff cell `(i,j)` holds value `k`),
subject to three `sum_eq … = 1` families: each cell takes exactly one value, each
value appears once per row, and each value once per column.  With no clues it is
satisfiable, so we form `latin_2_contradictory` from the 2×2 instance by adding two
clues that pin the two value-indicators of cell `(0,0)` — `x[0,0,0]` and `x[0,0,1]`
— *both* to `1`, i.e. "cell `(0,0)` is simultaneously value 1 and value 2".  That
contradicts cell `(0,0)`'s `sum_eq` (the cell's indicators must sum to exactly one),
so the puzzle is unsatisfiable — the canonical "a cell cannot hold two values" case.

The infeasibility uses only cell `(0,0)`'s `sum_eq` and the two `equals_const` clues,
all linear over `{0,1}`, so the proof rides the existing aux-free `encodeLinearLe`
through the generic spine `csp_unsat_generic`:

* `sum_eq_sat` — the new bridge (`Adapter.lean`): a satisfied `sum_eq scope t` gives
  `(scope.toList.map a).sum = t`; reducing the concrete cell scope yields `a 0 + a 1 ≤ 1`;
* `equals_const_sat` — reused from `Sudoku.lean`: each clue `equals_const v 1` pins `a v = 1`;
* `extend_sat_encodeLinearLe` — turns the cell bound `a 0 + a 1 ≤ 1` and each clue's
  `a v ≥ 1` half (encoded `-a v ≤ -1`) into PB constraints.

The signature carries all eight grid indicators (like pigeonhole/Sudoku carry every
variable); only cell `(0,0)`'s two indicators and the cell `sum_eq` participate in the
UNSAT core.
-/

/-- The contradictory-clue instance: the corpus 2×2 binary Latin square
    (`latin_square_csp 2`) with two clues pinning cell `(0,0)`'s value-1 and value-2
    indicators (variables 0 and 1) *both* to `1`, violating cell `(0,0)`'s `sum_eq`. -/
def latin_2_contradictory : IntCSP :=
  (latin_square_csp 2).addConstraints
    [equals_const ⟨0, by decide⟩ 1, equals_const ⟨1, by decide⟩ 1]

/-! ### The signature and PB encoding -/

/-- The PB signature: the eight indicator variables of the 2×2 binary Latin square,
    each Boolean (domain `{0,1}`, width 1), no Booleans or auxiliaries. -/
def latinSig : CSPSig where
  nInt := 8
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The PB user constraints: cell `(0,0)`'s `sum_eq` upper half `x[0,0,0] + x[0,0,1] ≤ 1`,
    plus the two clues `x[0,0,0] ≥ 1` and `x[0,0,1] ≥ 1` (encoded as `-x ≤ -1`; the
    matching `≤ 1` halves are domain tautologies, dropped by `normalize`).  All aux-free. -/
def latinUser : List (PBConstr (PBVar latinSig)) :=
  (normalize (encodeLinearLe [(1, (0:Fin 8)), (1, (1:Fin 8))] 1)).toList ++
  (normalize (encodeLinearLe [(-1, (0:Fin 8))] (-1))).toList ++
  (normalize (encodeLinearLe [(-1, (1:Fin 8))] (-1))).toList

/-- The veripb-elaborated kernel proof of UNSAT for `latinUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The eight width-1 indicators map to OPB
    `x1..x8`; the single threshold `a i ≤ 0` of indicator `i` is OPB `x{i+1}`, so the
    OPB reads `x1 + x2 ≥ 1` (the cell upper half), `~x1 ≥ 1`, `~x2 ≥ 1` (the two clues). -/
def latinKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 3;
rup >= 0 : ~ ;
rup 1 x2 >= 1 : ~ 2 1;
pol 3 5 +;
output NONE ;
conclusion UNSAT : 6;
end pseudo-Boolean proof;
"

/-- The PB encoding of the contradictory-clue Latin square is unsatisfiable —
    established by the external PB certificate, kernel-checked through PBLean's verified
    reflection checker (`native_decide` runs the checker; RoundingSat / veripb / the
    serializer are untrusted). -/
theorem latin_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((latinSig.monotonicity ++ latinUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 8 latinKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- **End-to-end Latin-square-with-contradictory-clues UNSAT.** The instance
    `latin_2_contradictory` (the corpus 2×2 binary Latin square with cell `(0,0)`'s two
    value indicators both clued to `1`) is unsatisfiable — discharged through the verified
    PB pipeline: the `sum_eq` bridge turns any solution into the cell bound
    `x[0,0,0] + x[0,0,1] ≤ 1`, the `equals_const` bridge pins both clued indicators to `1`,
    the generic spine `csp_unsat_generic` turns those into a PB model via the aux-free
    `encodeLinearLe` encoder, and the committed certificate `latin_formulaUnsat` contradicts
    it (two indicators cannot both be `1` while summing to at most `1`). -/
theorem latin_2_contradictory_unsat : ¬ latin_2_contradictory.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Expose the constraint list as the explicit append (defeq through `addConstraints`).
  have hsol' : ∀ c ∈ [equals_const (⟨0, by decide⟩ : Fin (latin_square_csp 2).num_vars) 1,
      equals_const (⟨1, by decide⟩ : Fin (latin_square_csp 2).num_vars) 1] ++
        (latin_square_csp 2).constraints,
      IntCSP.satisfiesConstraintInt c a := hsol
  -- Every indicator lies in `{0,1}` (from its `bound`).
  have hdom : ∀ i : Fin latinSig.nInt, a i ∈ latinSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 0 1) a := by
      apply hsol'
      apply List.mem_append_right
      show bound i 0 1 ∈ (latin_square_csp 2).constraints
      unfold latin_square_csp
      simp only []
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 0 1 a hb
    show a i ∈ domainValues 0 1
    exact mem_domainValues.mpr ⟨h1, h2⟩
  -- Cell (0,0)'s `sum_eq` bounds its two indicators: `a 0 + a 1 ≤ 1`.
  have hcell : a (0 : Fin 8) + a (1 : Fin 8) ≤ 1 := by
    have hc : IntCSP.satisfiesConstraintInt
        (sum_eq (indices_to_vector 8 (cell_value_indices 2 0 0) (by
          intro idx h_in
          have : idx ∈ (List.range 2).map (latin_idx 2 0 0) := h_in
          obtain ⟨k, hk, he⟩ := List.mem_map.mp this
          have : k < 2 := List.mem_range.mp hk
          rw [← he]; unfold latin_idx; omega)) 1) a := by
      apply hsol'
      apply List.mem_append_right
      show _ ∈ (latin_square_csp 2).constraints
      unfold latin_square_csp
      simp only []
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      rw [List.mem_flatMap]
      refine ⟨⟨0, by decide⟩, List.mem_finRange _, ?_⟩
      rw [List.mem_map]
      refine ⟨⟨0, by decide⟩, List.mem_finRange _, rfl⟩
    have hsum := sum_eq_sat _ 1 a hc
    -- the cell scope's `.toList` is definitionally `[0,1]` (proof-irrelevant)
    change (List.map a [(0 : Fin 8), (1 : Fin 8)]).sum = 1 at hsum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    linarith
  -- The two clues pin both indicators of cell (0,0) to 1.
  have hg0 : a (0 : Fin 8) = 1 :=
    equals_const_sat _ 1 a (hsol' _ (List.mem_append_left _ List.mem_cons_self))
  have hg1 : a (1 : Fin 8) = 1 :=
    equals_const_sat _ 1 a
      (hsol' _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  -- The generic spine rules out any in-domain solution with the cell bound and both clues.
  have key : ¬ ∃ (a : Fin latinSig.nInt → Int) (_ : Fin latinSig.nBool → Bool),
      (∀ i, a i ∈ latinSig.values i) ∧
      (a (0 : Fin 8) + a (1 : Fin 8) ≤ 1 ∧ a (0 : Fin 8) = 1 ∧ a (1 : Fin 8) = 1) := by
    apply csp_unsat_generic latinSig latinUser
      (fun a _ => a (0 : Fin 8) + a (1 : Fin 8) ≤ 1 ∧ a (0 : Fin 8) = 1 ∧ a (1 : Fin 8) = 1)
      (fun _ _ _ => false)
    · intro a' bA hdom' hP c hc
      obtain ⟨hcell', hq0, hq1⟩ := hP
      unfold latinUser at hc
      rw [List.mem_append, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · rw [Option.mem_toList] at hc
        refine extend_sat_encodeLinearLe a' bA _ hdom' [(1, (0:Fin 8)), (1, (1:Fin 8))] 1 c hc ?_
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
      · rw [Option.mem_toList] at hc
        refine extend_sat_encodeLinearLe a' bA _ hdom' [(-1, (0:Fin 8))] (-1) c hc ?_
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
      · rw [Option.mem_toList] at hc
        refine extend_sat_encodeLinearLe a' bA _ hdom' [(-1, (1:Fin 8))] (-1) c hc ?_
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · exact latin_formulaUnsat
  exact key ⟨a, fun _ => false, hdom, hcell, hg0, hg1⟩

end CSP.L2S.PB.Latin
