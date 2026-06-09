import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«19_sudoku»

namespace CSP.L2S.PB.Sudoku

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for a Sudoku with contradictory givens

This is the **first `equals_const` (fixed-value / "givens") consumer** of the PB
pipeline, opening the Sudoku / Latin-square-with-clues family.  The corpus parametric
puzzle `sudoku_csp` (`Tests/lean/19_sudoku.lean`) is satisfiable with no clues, so we
form the instance `sudoku_4_bad` by adding two clues that violate a Sudoku rule: a 4×4
grid (domain `{1,2,3,4}`) with the first two cells of row 0 *both* clued to `1`.  Two
equal entries in one row contradict that row's `alldifferent`, so the puzzle is
unsatisfiable — exactly the "conflicting clues" case a Sudoku solver must reject.

The infeasibility uses only row 0's `alldifferent` and the two `equals_const` clues, so
the proof rides the existing aux-free `encodeAllDifferent` (as in pigeonhole) plus the
linear `encodeLinearLe` for the clues, through the generic spine `csp_unsat_generic`:

* `equals_const_sat` — the reusable bridge (in `NotAllEqualBridge.lean`, beside its twin
  `not_equals_const_sat`): a satisfied `equals_const v c` constraint pins `a v = c`;
* `alldifferent_sat` / `extend_sat_encodeAllDifferent` — reused verbatim from
  pigeonhole / graph-colouring;
* `extend_sat_encodeLinearLe` — turns each clue `a v = 1` into the linear `a v ≤ 1`
  (the `a v ≥ 1` half is a domain tautology, dropped by `normalize`).

The signature carries all 16 grid variables (like pigeonhole carries every pigeon); only
row 0's four thresholds and the two clue constraints participate in the UNSAT core.
-/

/-- The contradictory-clue instance: the corpus 4×4 Sudoku (`sudoku_4`) with two clues
    that both pin row 0's first two cells (variables 0 and 1) to the digit `1`, violating
    row 0's `alldifferent`. -/
def sudoku_4_contradictory : IntCSP :=
  sudoku_4.addConstraints [equals_const ⟨0, by decide⟩ 1, equals_const ⟨1, by decide⟩ 1]

/-! ### The signature and PB encoding -/

/-- The PB signature: the 16 grid variables of the 4×4 Sudoku, each over the digit
    domain `{1,2,3,4}` (width 3), no Booleans or auxiliaries. -/
def sudokuSig : CSPSig where
  nInt := 16
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 4
  sorted := fun _ => domainValues_sorted 1 4
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Row 0's four cells `[0,1,2,3]` — the scope of the `alldifferent` that the two clues
    contradict (defeq to `(row_variables 4 0).toList`). -/
def sudokuRow0 : List (Fin sudokuSig.nInt) :=
  [(0:Fin 16), (1:Fin 16), (2:Fin 16), (3:Fin 16)]

/-- The PB user constraints: row 0's normalized `alldifferent` per-value cardinality
    constraints over `{1,2,3,4}`, plus the two clues `a 0 ≤ 1` and `a 1 ≤ 1` (the `≥ 1`
    halves are domain tautologies, dropped by `normalize`).  All aux-free. -/
def sudokuUser : List (PBConstr (PBVar sudokuSig)) :=
  (encodeAllDifferent sudokuRow0 [1, 2, 3, 4]).filterMap normalize ++
  (normalize (encodeLinearLe [(1, (0:Fin 16))] 1)).toList ++
  (normalize (encodeLinearLe [(1, (1:Fin 16))] 1)).toList

/-- The veripb-elaborated kernel proof of UNSAT for `sudokuUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The 16 cells (width 3) map to OPB
    `x1..x48`, threshold `a i ≤ k` of cell `i` to `x{3i+k}`. -/
def sudokuKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 38;
rup >= 0 : ~ ;
rup 1 x1 >= 1 : ~ 37;
rup 1 x2 >= 1 : ~ 37;
rup 1 x3 >= 1 : ~ 37;
rup 1 ~x4 >= 1 : ~ 40 33;
rup 1 ~x7 >= 1 : ~ 40 33;
rup 1 ~x10 >= 1 : ~ 40 33;
pol 38 43 +;
output NONE ;
conclusion UNSAT : 46;
end pseudo-Boolean proof;
"

/-- The PB encoding of the contradictory-clue Sudoku is unsatisfiable — established by
    the external PB certificate, kernel-checked through PBLean's verified reflection
    checker (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem sudoku_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((sudokuSig.monotonicity ++ sudokuUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 48 sudokuKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- **End-to-end Sudoku-with-contradictory-clues UNSAT.** The instance
    `sudoku_4_contradictory` (the corpus 4×4 Sudoku with two row-0 cells both clued to
    `1`) is unsatisfiable — discharged through the verified PB pipeline: the
    `alldifferent` bridge turns any solution into pairwise-distinct row-0 values, the
    `equals_const` bridge pins the two clued cells to `1`, the generic spine
    `csp_unsat_generic` turns those into a PB model via the aux-free `encodeAllDifferent`
    / `encodeLinearLe` encoders, and the committed certificate `sudoku_formulaUnsat`
    contradicts it (two `1`s cannot be distinct). -/
theorem sudoku_4_contradictory_unsat : ¬ sudoku_4_contradictory.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Expose the constraint list as the explicit append (defeq through `addConstraints`).
  have hsol' : ∀ c ∈ [equals_const (⟨0, by decide⟩ : Fin sudoku_4.num_vars) 1,
      equals_const (⟨1, by decide⟩ : Fin sudoku_4.num_vars) 1] ++ sudoku_4.constraints,
      IntCSP.satisfiesConstraintInt c a := hsol
  -- Every grid cell lies in the digit domain {1,2,3,4} (from its `bound`).
  have hdom : ∀ i : Fin sudokuSig.nInt, a i ∈ sudokuSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 1 (4:ℕ)) a := by
      apply hsol'
      apply List.mem_append_right
      show bound i 1 (4:ℕ) ∈ sudoku_4.constraints
      unfold sudoku_4 sudoku_csp
      simp only []
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 1 (4:ℕ) a hb
    have h2' : a i ≤ 4 := by exact_mod_cast h2
    show a i ∈ domainValues 1 4
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- Row 0's cells are pairwise distinct (from its `alldifferent`).
  have hnodup : (sudokuRow0.map a).Nodup := by
    have ha : IntCSP.satisfiesConstraintInt (alldifferent (row_variables 4 0)) a := by
      apply hsol'
      apply List.mem_append_right
      show alldifferent (row_variables 4 0) ∈ sudoku_4.constraints
      unfold sudoku_4 sudoku_csp
      simp only []
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
      exact List.mem_map.mpr ⟨(0:Fin 4), List.mem_finRange 0, rfl⟩
    exact alldifferent_sat (row_variables 4 0) a ha
  -- The two clues pin cells 0 and 1 to the digit 1.
  have hg0 : a (0:Fin 16) = 1 :=
    equals_const_sat _ 1 a (hsol' _ (List.mem_append_left _ List.mem_cons_self))
  have hg1 : a (1:Fin 16) = 1 :=
    equals_const_sat _ 1 a
      (hsol' _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  -- The generic spine rules out any in-domain solution with distinct row 0 and both clues.
  have key : ¬ ∃ (a : Fin sudokuSig.nInt → Int) (_ : Fin sudokuSig.nBool → Bool),
      (∀ i, a i ∈ sudokuSig.values i) ∧
      ((sudokuRow0.map a).Nodup ∧ a (0:Fin 16) = 1 ∧ a (1:Fin 16) = 1) := by
    apply csp_unsat_generic sudokuSig sudokuUser
      (fun a _ => (sudokuRow0.map a).Nodup ∧ a (0:Fin 16) = 1 ∧ a (1:Fin 16) = 1)
      (fun _ _ _ => false)
    · intro a' bA hdom' hP c hc
      obtain ⟨hnd, hq0, hq1⟩ := hP
      unfold sudokuUser at hc
      rw [List.mem_append, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · exact extend_sat_encodeAllDifferent a' bA _ hdom' sudokuRow0 [1, 2, 3, 4] c hc hnd
      · rw [Option.mem_toList] at hc
        refine extend_sat_encodeLinearLe a' bA _ hdom' [(1, (0:Fin 16))] 1 c hc ?_
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
      · rw [Option.mem_toList] at hc
        refine extend_sat_encodeLinearLe a' bA _ hdom' [(1, (1:Fin 16))] 1 c hc ?_
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · exact sudoku_formulaUnsat
  exact key ⟨a, fun _ => false, hdom, hnodup, hg0, hg1⟩

end CSP.L2S.PB.Sudoku
