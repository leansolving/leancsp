import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«08_queens»

namespace CSP.L2S.PB.BlockedQueens

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for a blocked N-Queens instance

*Blocked / completion N-Queens* is plain N-Queens with some squares forbidden (blocked);
it is UNSAT exactly when the restriction destroys every completion.  We reuse the corpus
N-Queens model `nqueens_csp 4` (`Tests/lean/08_queens.lean`) — one variable per row giving
that row's column in `{{1,2,3,4}}`, with `alldifferent` on columns and the two diagonal
constraints — and **block the entire first column** by adding `not_equals_const a i 1` for
every row `i` (no queen may sit in column `1`).

The corpus `nqueens_csp 4` is satisfiable (the 4-queens puzzle has two solutions), so the
blocked instance `blockedQueens4` is a genuine restriction.  It is unsatisfiable by a
counting argument that uses only the **columns**: the four rows take four *distinct*
columns from `{{1,2,3,4}}` (`alldifferent`), but none may be column `1` (the blocks), so the
four columns must come from the three values `{{2,3,4}}` — impossible.  The diagonal
constraints are part of the (faithful) model but are not needed for this refutation.

## Encoding

The infeasibility uses only the columns `alldifferent` and the four `not_equals_const`
blocks, so the proof rides the existing aux-free encoders through the generic spine
`csp_unsat_generic`:

* `not_equals_const_sat` — the reusable bridge (in `NotAllEqualBridge.lean`): a satisfied
  `not_equals_const v c` constraint gives `a v ≠ c`;
* `alldifferent_sat` / `extend_sat_encodeAllDifferent` — reused from pigeonhole;
* `extend_sat_encodeNeConst` — turns each block `a i ≠ 1` into the aux-free `≠`-encoding.

The signature carries the four row variables over the column domain `{{1,2,3,4}}` (width 3),
so row `i` maps to OPB thresholds `x{{3i+1..3i+3}}` (12 variables).
-/

/-- The blocked instance: the corpus 4-queens CSP with the first column forbidden in every
    row (`not_equals_const a i 1` for `i = 0,1,2,3`). -/
def blockedQueens4 : IntCSP :=
  (nqueens_csp 4).addConstraints
    [not_equals_const (⟨0, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
     not_equals_const (⟨1, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
     not_equals_const (⟨2, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
     not_equals_const (⟨3, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1]

/-! ### The signature and PB encoding -/

/-- The PB signature: the four row variables of the 4-queens board, each over the column
    domain `{1,2,3,4}` (width 3), no Booleans or auxiliaries. -/
def bqSig : CSPSig where
  nInt := 4
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 4
  sorted := fun _ => domainValues_sorted 1 4
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The columns scope (`Vector.ofFn id` = `[0,1,2,3]`): the rows whose columns are all
    different. -/
def bqScope : _root_.Vector (VarType 4) 4 := _root_.Vector.ofFn id

/-- The four row variables as a `List (Fin bqSig.nInt)` (definitionally `[0,1,2,3]`). -/
def bqVars : List (Fin bqSig.nInt) := bqScope.toList

/-- The PB user constraints: the columns `alldifferent` per-value cardinality clauses over
    `{1,2,3,4}`, plus the four blocks `a i ≠ 1`.  All aux-free. -/
def bqUser : List (PBConstr (PBVar bqSig)) :=
  (encodeAllDifferent bqVars [1, 2, 3, 4]).filterMap normalize ++
  (normalize (encodeNeConst (0 : Fin 4) 1)).toList ++
  (normalize (encodeNeConst (1 : Fin 4) 1)).toList ++
  (normalize (encodeNeConst (2 : Fin 4) 1)).toList ++
  (normalize (encodeNeConst (3 : Fin 4) 1)).toList

/-- The veripb-elaborated kernel proof of UNSAT for `bqUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The four rows (width 3) map to OPB `x1..x12`. -/
def bqKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 16;
rup >= 0 : ~ ;
rup 1000000000000000 ~x1 1000000000000000 ~x4 1000000000000000 ~x7 1000000000000000 ~x10 >= 4000000000000000 : 14 16 13 15 ~;
pol 17 10 1000000000000000 * + 11 1000000000000000 * + 12 1000000000000000 * + 18 +;
output NONE ;
conclusion UNSAT : 19;
end pseudo-Boolean proof;
"

/-- The PB encoding of the blocked 4-queens instance is unsatisfiable — established by the
    external PB certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem bq_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((bqSig.monotonicity ++ bqUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 12 bqKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- **End-to-end blocked-N-Queens UNSAT.** The instance `blockedQueens4` (the corpus
    4-queens CSP with column `1` forbidden in every row) is unsatisfiable — discharged
    through the verified PB pipeline: the columns `alldifferent` bridge gives the four
    distinct columns, the `not_equals_const` bridge forbids column `1` in each row, the
    generic spine `csp_unsat_generic` turns those into a PB model via the aux-free
    `encodeAllDifferent` / `encodeNeConst` encoders, and the committed certificate
    `bq_formulaUnsat` contradicts it (four distinct columns cannot avoid `1` within
    `{1,2,3,4}`). -/
theorem blocked_queens_4_unsat : ¬ blockedQueens4.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Expose the constraint list as the explicit append (defeq through `addConstraints`).
  have hsol' : ∀ c ∈ [not_equals_const (⟨0, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
      not_equals_const (⟨1, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
      not_equals_const (⟨2, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1,
      not_equals_const (⟨3, by decide⟩ : Fin (nqueens_csp 4).num_vars) 1] ++
      (nqueens_csp 4).constraints, IntCSP.satisfiesConstraintInt c a := hsol
  -- Every row's column lies in {1,2,3,4} (from its `bound`).
  have hdom : ∀ i : Fin bqSig.nInt, a i ∈ bqSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 1 (4 : ℕ)) a := by
      apply hsol'
      apply List.mem_append_right
      show bound i 1 (4 : ℕ) ∈ queens_bounds 4 ++
        [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 4, alldifferent_diag_neg 4]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 1 (4 : ℕ) a hb
    have h2' : a i ≤ 4 := by exact_mod_cast h2
    show a i ∈ domainValues 1 4
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- The four columns are pairwise distinct (from the columns `alldifferent`).
  have hnodup : (bqVars.map a).Nodup := by
    have ha : IntCSP.satisfiesConstraintInt (alldifferent (_root_.Vector.ofFn id)) a := by
      apply hsol'
      apply List.mem_append_right
      show alldifferent (_root_.Vector.ofFn id) ∈ queens_bounds 4 ++
        [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 4, alldifferent_diag_neg 4]
      apply List.mem_append_right
      exact List.mem_cons_self
    exact alldifferent_sat bqScope a ha
  -- The four blocks forbid column 1 in each row.
  have hb0 : a (0 : Fin 4) ≠ 1 :=
    not_equals_const_sat _ 1 a (hsol' _ (List.mem_append_left _ List.mem_cons_self))
  have hb1 : a (1 : Fin 4) ≠ 1 :=
    not_equals_const_sat _ 1 a
      (hsol' _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hb2 : a (2 : Fin 4) ≠ 1 :=
    not_equals_const_sat _ 1 a
      (hsol' _ (List.mem_append_left _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hb3 : a (3 : Fin 4) ≠ 1 :=
    not_equals_const_sat _ 1 a
      (hsol' _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))))
  -- The generic spine rules out any in-domain solution with distinct columns all ≠ 1.
  have key : ¬ ∃ (a : Fin bqSig.nInt → Int) (_ : Fin bqSig.nBool → Bool),
      (∀ i, a i ∈ bqSig.values i) ∧
      ((bqVars.map a).Nodup ∧ a (0 : Fin 4) ≠ 1 ∧ a (1 : Fin 4) ≠ 1 ∧
        a (2 : Fin 4) ≠ 1 ∧ a (3 : Fin 4) ≠ 1) := by
    apply csp_unsat_generic bqSig bqUser
      (fun a _ => (bqVars.map a).Nodup ∧ a (0 : Fin 4) ≠ 1 ∧ a (1 : Fin 4) ≠ 1 ∧
        a (2 : Fin 4) ≠ 1 ∧ a (3 : Fin 4) ≠ 1)
      (fun _ _ _ => false)
    · intro a' bA hdom' hP c hc
      obtain ⟨hnd, h0, h1, h2, h3⟩ := hP
      unfold bqUser at hc
      rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hc
      rcases hc with (((hc | hc) | hc) | hc) | hc
      · exact extend_sat_encodeAllDifferent a' bA _ hdom' bqVars [1, 2, 3, 4] c hc hnd
      · rw [Option.mem_toList] at hc
        exact extend_sat_encodeNeConst a' bA _ hdom' (0 : Fin 4) 1 h0 c hc
      · rw [Option.mem_toList] at hc
        exact extend_sat_encodeNeConst a' bA _ hdom' (1 : Fin 4) 1 h1 c hc
      · rw [Option.mem_toList] at hc
        exact extend_sat_encodeNeConst a' bA _ hdom' (2 : Fin 4) 1 h2 c hc
      · rw [Option.mem_toList] at hc
        exact extend_sat_encodeNeConst a' bA _ hdom' (3 : Fin 4) 1 h3 c hc
    · exact bq_formulaUnsat
  exact key ⟨a, fun _ => false, hdom, hnodup, hb0, hb1, hb2, hb3⟩

end CSP.L2S.PB.BlockedQueens
