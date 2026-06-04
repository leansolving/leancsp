import CSP.L2S.Backends.PB.LinearNe
import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«08_queens»

namespace CSP.L2S.PB.NQueens

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for `nqueens_csp 2` and `nqueens_csp 3`

This file proves both the 2×2 and 3×3 N-Queens corpus instances unsatisfiable
through the verified PB pipeline.  The 2×2 case (below) is the minimal
`encodeLinearNe` showcase; the 3×3 case (further down) scales up to a
multi-variable `alldifferent` (columns) mixed with six Big-M diagonal
disequalities.

`nqueens_csp 2` (`Tests/lean/08_queens.lean`) places two queens on a 2×2 board:
two row variables `a 0, a 1 ∈ {1,2}` (one per column), with

* the **columns** `alldifferent (Vector.ofFn id)` constraint → `a 0 ≠ a 1`;
* the **positive-diagonal** `alldifferent_diag_pos 2` → `a 0 + 0 ≠ a 1 + 1`, i.e.
  `a 0 ≠ a 1 + 1`;
* the **negative-diagonal** `alldifferent_diag_neg 2` → `a 0 - 0 ≠ a 1 - 1`, i.e.
  `a 0 ≠ a 1 - 1`.

Every pair of cells on a 2×2 board shares a row, column, or diagonal, so the
instance is unsatisfiable.  Writing `d := a 0 - a 1`, the three constraints say
`d ≠ 0`, `d ≠ 1`, `d ≠ -1`; but `a 0, a 1 ∈ {1,2}` forces `d ∈ {-1,0,1}`.

This is the **first end-to-end consumer of `encodeLinearNe`** (the general Big-M
linear-disequality encoder, `LinearNe.lean`) and the **first multi-aux instance**:
all three constraints are `Σ = a 0 - a 1 ≠ b` with the same term list
`[(1, 0), (-1, 1)]` and `b ∈ {0, 1, -1}`, each carrying its own selector `aux`,
so `nAux = 3`.  They ride the generic spine `csp_unsat_generic` through three
`extend_sat_encodeLinearNe` applications whose selectors are set from the
solution by `nqAux`.
-/

/-- Pointwise evaluation of an `ofFn` vector (the `alldifferent` / diagonal scopes
    are `Vector.ofFn id`).  Core `Vector.get` is `Array`-backed, so this unfolds
    through `toArray_ofFn` / `Array.getElem_ofFn` (cf. `NQueensEquivalence`). -/
private theorem vget {α : Type} {m : ℕ} (f : Fin m → α) (k : Fin m) :
    (_root_.Vector.ofFn f).get k = f k := by
  simp only [_root_.Vector.get, _root_.Vector.toArray_ofFn, Array.getElem_ofFn,
    Fin.val_cast, Fin.eta]

/-! ### The signature and shared linear form -/

/-- The PB signature for `nqueens_csp 2`: two integer (row) variables over the
    domain `{1,2}`, no Booleans, three Big-M selector auxiliaries (one per `≠`
    constraint). -/
def nqSig : CSPSig where
  nInt := 2
  nBool := 0
  nAux := 3
  values := fun _ => domainValues 1 2
  sorted := fun _ => domainValues_sorted 1 2
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The shared linear form `Σ = a 0 - a 1` (coefficient `+1` on var 0, `-1` on
    var 1). -/
def nqTerms : List (Int × Fin nqSig.nInt) := [(1, (0 : Fin 2)), (-1, (1 : Fin 2))]

/-- The linear form evaluated on an assignment is `a 0 - a 1`. -/
theorem nqSum (a : Fin nqSig.nInt → Int) :
    (nqTerms.map (fun p => p.1 * a p.2)).sum = a (0 : Fin 2) - a (1 : Fin 2) := by
  simp only [nqTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- The selector auxiliaries set from a solution: `aux k` records whether the
    linear sum exceeds the `k`-th bound (`0`, `1`, `-1`), exactly as
    `encodeLinearNe`'s soundness requires. -/
def nqAux (a : Fin nqSig.nInt → Int) (_ : Fin nqSig.nBool → Bool) : Fin nqSig.nAux → Bool :=
  fun s => decide ((nqTerms.map (fun p => p.1 * a p.2)).sum >
    (if s = (0 : Fin 3) then 0 else if s = (1 : Fin 3) then 1 else -1))

/-- The PB user constraints: the Big-M disequality encodings of the three
    `Σ = a 0 - a 1 ≠ b` constraints (`b = 0` columns, `b = 1` positive diagonal,
    `b = -1` negative diagonal), each with its own selector aux.  The
    order-encoding staircase clauses are supplied by the spine (empty here, since
    each variable has the single-threshold binary domain). -/
def nqUser : List (PBConstr (PBVar nqSig)) :=
  ((encodeLinearNe nqTerms 0 (0 : Fin 3)).filterMap normalize) ++
  ((encodeLinearNe nqTerms 1 (1 : Fin 3)).filterMap normalize) ++
  ((encodeLinearNe nqTerms (-1) (2 : Fin 3)).filterMap normalize)

/-! ### Corpus bridges: the three constraints become disequalities on `a 0, a 1` -/

/-- **Bridge.** The columns `alldifferent (Vector.ofFn id)` constraint makes the
    two row values differ.  Reduces the arity-2 `Nodup` checker directly (the
    scope `Vector.ofFn id` evaluates pointwise via `vget`). -/
theorem nq_cols_sat (a : HomogeneousAssignment 2)
    (h : HomogeneousCSP.satisfiesConstraint (alldifferent (_root_.Vector.ofFn id)) a) :
    a (0 : Fin 2) ≠ a (1 : Fin 2) := by
  simp only [HomogeneousCSP.satisfiesConstraint, alldifferent,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    CSP.map_assignment, extractValues, vget, id_eq, decide_eq_true_eq,
    List.ofFn_succ, List.ofFn_zero, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, or_false, and_true, not_false_eq_true] at h
  exact h

/-- **Bridge.** The positive-diagonal `alldifferent_diag_pos 2` constraint makes
    `a 0 + 0` and `a 1 + 1` differ, i.e. `a 0 ≠ a 1 + 1`. -/
theorem nq_diag_pos_sat (a : HomogeneousAssignment 2)
    (h : HomogeneousCSP.satisfiesConstraint (alldifferent_diag_pos 2) a) :
    a (0 : Fin 2) ≠ a (1 : Fin 2) + 1 := by
  simp only [HomogeneousCSP.satisfiesConstraint, alldifferent_diag_pos,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    CSP.map_assignment, vget, decide_eq_true_eq,
    List.ofFn_succ, List.ofFn_zero, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, or_false, and_true, not_false_eq_true,
    Fin.val_succ, Fin.val_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_add, add_zero] at h
  exact h

/-- **Bridge.** The negative-diagonal `alldifferent_diag_neg 2` constraint makes
    `a 0 - 0` and `a 1 - 1` differ, i.e. `a 0 ≠ a 1 - 1`. -/
theorem nq_diag_neg_sat (a : HomogeneousAssignment 2)
    (h : HomogeneousCSP.satisfiesConstraint (alldifferent_diag_neg 2) a) :
    a (0 : Fin 2) ≠ a (1 : Fin 2) - 1 := by
  simp only [HomogeneousCSP.satisfiesConstraint, alldifferent_diag_neg,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    CSP.map_assignment, vget, decide_eq_true_eq,
    List.ofFn_succ, List.ofFn_zero, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, or_false, and_true, not_false_eq_true,
    Fin.val_succ, Fin.val_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_add, sub_zero] at h
  exact h

/-! ### The PB certificate -/

/-- The veripb-elaborated kernel proof of UNSAT for `nqUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The thresholds `a 0 ≤ 1`, `a 1 ≤ 1`
    map to OPB `x1, x2`; the three selectors to `x3, x4, x5`; the six clauses are
    the Big-M disequalities. -/
def nqKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 6;
rup >= 0 : ~ ;
pol 1 s;
pol 2 s;
pol 3 s;
pol 4 s;
rup 1 ~x4 >= 1 : ~ 11;
pol 5 s;
rup 1 x5 >= 1 : ~ 13;
pol 6 14 6 * +;
pbc 1000000000000000 x1 1000000000000000 x3 >= 1000000000000000 : subproof
pol 16 8 1000000000000000 * + 1000000000000000 d;
pol 16 17 1000000000000000 * +;
qed : 18;
pbc 1000000000000000 x1 1000000000000000 x3 >= 1000000000000000 : subproof
pol 20 8 1000000000000000 * + 1000000000000000 d;
pol 20 21 1000000000000000 * +;
qed : 22;
pol 19 1000000000000000 d;
pol 19 1000000000000000 d;
pol 9 10 + 12 + s;
rup 1 x1 >= 1 : ~ 26 8;
rup 1 ~x2 >= 1 : ~ 26 8;
rup 1 x1 1 ~x2 >= 2 : 27 28 ~;
pol 15 29 +;
output NONE ;
conclusion UNSAT : 30;
end pseudo-Boolean proof;
"

/-- The PB encoding of `nqueens_csp 2` is unsatisfiable — established by the
    external PB certificate, kernel-checked through PBLean's verified reflection
    checker (`native_decide` runs the checker; RoundingSat / veripb / the
    serializer are untrusted). -/
theorem nq_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((nqSig.monotonicity ++ nqUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 5 nqKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain row assignment that places the two
    queens non-attacking (distinct rows and distinct diagonals). -/
theorem nq_no_sol : ¬ ∃ (a : Fin nqSig.nInt → Int) (_ : Fin nqSig.nBool → Bool),
    (∀ i, a i ∈ nqSig.values i) ∧
    (a (0 : Fin 2) ≠ a (1 : Fin 2) ∧
     a (0 : Fin 2) ≠ a (1 : Fin 2) + 1 ∧
     a (0 : Fin 2) ≠ a (1 : Fin 2) - 1) := by
  apply csp_unsat_generic nqSig nqUser
    (fun a _ => a (0 : Fin 2) ≠ a (1 : Fin 2) ∧
      a (0 : Fin 2) ≠ a (1 : Fin 2) + 1 ∧ a (0 : Fin 2) ≠ a (1 : Fin 2) - 1)
    nqAux
  · intro a bA hdom hP c hc
    obtain ⟨hP1, hP2, hP3⟩ := hP
    simp only [nqUser, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · -- columns: a 0 - a 1 ≠ 0
      refine extend_sat_encodeLinearNe a bA (nqAux a bA) hdom nqTerms 0 (0 : Fin 3) ?_ rfl c hc
      rw [nqSum]; omega
    · -- positive diagonal: a 0 - a 1 ≠ 1
      refine extend_sat_encodeLinearNe a bA (nqAux a bA) hdom nqTerms 1 (1 : Fin 3) ?_ rfl c hc
      rw [nqSum]; omega
    · -- negative diagonal: a 0 - a 1 ≠ -1
      refine extend_sat_encodeLinearNe a bA (nqAux a bA) hdom nqTerms (-1) (2 : Fin 3) ?_ rfl c hc
      rw [nqSum]; omega
  · exact nq_formulaUnsat

/-- **End-to-end N-Queens UNSAT.** The corpus CSP `nqueens_csp 2` — place two
    queens on a 2×2 board with no shared row, column, or diagonal — is
    unsatisfiable, discharged through the verified PB pipeline: the columns and
    two diagonal bridges turn any solution into the three `≠` facts on
    `a 0, a 1`, the generic spine `csp_unsat_generic` turns those into a PB model
    via the Big-M `encodeLinearNe` encoding, and the committed certificate
    `nq_formulaUnsat` contradicts it. -/
theorem nqueens_2_unsat : ¬ (nqueens_csp 2).isSatisfiable := by
  rintro ⟨a, hsol⟩
  -- Every row lies in `{1,2}` (from its `bound`).
  have hdom : ∀ i : Fin nqSig.nInt, a i ∈ nqSig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (2 : ℕ)) a := by
      apply hsol
      show bound i 1 (2 : ℕ) ∈ queens_bounds 2 ++
        [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 2, alldifferent_diag_neg 2]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 1 (2 : ℕ) a hb
    have h2' : a i ≤ 2 := by exact_mod_cast h2
    show a i ∈ domainValues 1 2
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- The three non-attacking facts (from the columns / diagonal constraints).
  have hCols : a (0 : Fin 2) ≠ a (1 : Fin 2) := by
    refine nq_cols_sat a (hsol _ ?_)
    show alldifferent (_root_.Vector.ofFn id) ∈ queens_bounds 2 ++
      [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 2, alldifferent_diag_neg 2]
    apply List.mem_append_right; exact List.mem_cons_self
  have hDiagP : a (0 : Fin 2) ≠ a (1 : Fin 2) + 1 := by
    refine nq_diag_pos_sat a (hsol _ ?_)
    show alldifferent_diag_pos 2 ∈ queens_bounds 2 ++
      [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 2, alldifferent_diag_neg 2]
    apply List.mem_append_right; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hDiagN : a (0 : Fin 2) ≠ a (1 : Fin 2) - 1 := by
    refine nq_diag_neg_sat a (hsol _ ?_)
    show alldifferent_diag_neg 2 ∈ queens_bounds 2 ++
      [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 2, alldifferent_diag_neg 2]
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact nq_no_sol ⟨a, fun _ => false, hdom, hCols, hDiagP, hDiagN⟩


/-! ## A larger instance: `nqueens_csp 3` (three queens on a 3×3 board)

The 3-queens problem is unsatisfiable (the N-Queens problem has solutions only
for `n = 1` and `n ≥ 4`).  Compared with `nqueens_csp 2`, this instance exercises
the **multi-variable `alldifferent`** for the columns (three rows over the domain
`{1,2,3}`, width 2, so `monotonicity` is non-empty) mixed with **six Big-M linear
disequalities** for the diagonals: each diagonal `alldifferent` is now a
*three-element* `Nodup`, contributing three pairwise diagonal constraints
`a i + i ≠ a j + j`.  Columns ride the aux-free `encodeAllDifferent` (reusing the
`alldifferent_sat` / `extend_sat_encodeAllDifferent` bridges from `Pigeonhole`),
the diagonals ride `encodeLinearNe` with one selector aux each (`nAux = 6`). -/

/-- The PB signature for `nqueens_csp 3`: three integer (row) variables over the
    domain `{1,2,3}`, no Booleans, and six Big-M selector auxiliaries (one per
    diagonal disequality). -/
def nq3Sig : CSPSig where
  nInt := 3
  nBool := 0
  nAux := 6
  values := fun _ => domainValues 1 3
  sorted := fun _ => domainValues_sorted 1 3
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Linear form `a 0 - a 1` (the `(0,1)` variable pair). -/
def nq3Terms01 : List (Int × Fin nq3Sig.nInt) := [(1, (0 : Fin 3)), (-1, (1 : Fin 3))]
/-- Linear form `a 0 - a 2` (the `(0,2)` variable pair). -/
def nq3Terms02 : List (Int × Fin nq3Sig.nInt) := [(1, (0 : Fin 3)), (-1, (2 : Fin 3))]
/-- Linear form `a 1 - a 2` (the `(1,2)` variable pair). -/
def nq3Terms12 : List (Int × Fin nq3Sig.nInt) := [(1, (1 : Fin 3)), (-1, (2 : Fin 3))]

/-- The `(0,1)` linear form evaluated on an assignment is `a 0 - a 1`. -/
theorem nq3Sum01 (a : Fin nq3Sig.nInt → Int) :
    (nq3Terms01.map (fun p => p.1 * a p.2)).sum = a (0 : Fin 3) - a (1 : Fin 3) := by
  simp only [nq3Terms01, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- The `(0,2)` linear form evaluated on an assignment is `a 0 - a 2`. -/
theorem nq3Sum02 (a : Fin nq3Sig.nInt → Int) :
    (nq3Terms02.map (fun p => p.1 * a p.2)).sum = a (0 : Fin 3) - a (2 : Fin 3) := by
  simp only [nq3Terms02, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- The `(1,2)` linear form evaluated on an assignment is `a 1 - a 2`. -/
theorem nq3Sum12 (a : Fin nq3Sig.nInt → Int) :
    (nq3Terms12.map (fun p => p.1 * a p.2)).sum = a (1 : Fin 3) - a (2 : Fin 3) := by
  simp only [nq3Terms12, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- The column variables as the scope of the corpus `alldifferent` (`Vector.ofFn id`). -/
def nq3Scope : _root_.Vector (HomogeneousVarIndex 3) 3 := _root_.Vector.ofFn id

/-- The column variable list `[0,1,2]` (the `alldifferent` scope as a `List`). -/
def nq3Vars : List (Fin nq3Sig.nInt) := nq3Scope.toList

/-- The six diagonal selector auxiliaries set from a solution: `aux k` records
    whether the `k`-th diagonal linear sum exceeds its bound, as
    `encodeLinearNe`'s soundness requires (pos `(0,1),(0,2),(1,2)` then neg). -/
def nq3Aux (a : Fin nq3Sig.nInt → Int) (_ : Fin nq3Sig.nBool → Bool) : Fin nq3Sig.nAux → Bool :=
  fun s =>
    if s = (0 : Fin 6) then decide ((nq3Terms01.map (fun p => p.1 * a p.2)).sum > 1)
    else if s = (1 : Fin 6) then decide ((nq3Terms02.map (fun p => p.1 * a p.2)).sum > 2)
    else if s = (2 : Fin 6) then decide ((nq3Terms12.map (fun p => p.1 * a p.2)).sum > 1)
    else if s = (3 : Fin 6) then decide ((nq3Terms01.map (fun p => p.1 * a p.2)).sum > -1)
    else if s = (4 : Fin 6) then decide ((nq3Terms02.map (fun p => p.1 * a p.2)).sum > -2)
    else decide ((nq3Terms12.map (fun p => p.1 * a p.2)).sum > -1)

/-- The PB user constraints for `nqueens_csp 3`: the six Big-M diagonal
    disequalities (positive `a i - a j ≠ j - i` for `(0,1),(0,2),(1,2)`, then the
    negative `a i - a j ≠ i - j`), each with its own selector aux, followed by the
    aux-free columns `encodeAllDifferent` over `{1,2,3}`. -/
def nq3User : List (PBConstr (PBVar nq3Sig)) :=
  ((encodeLinearNe nq3Terms01 1 (0 : Fin 6)).filterMap normalize) ++
  ((encodeLinearNe nq3Terms02 2 (1 : Fin 6)).filterMap normalize) ++
  ((encodeLinearNe nq3Terms12 1 (2 : Fin 6)).filterMap normalize) ++
  ((encodeLinearNe nq3Terms01 (-1) (3 : Fin 6)).filterMap normalize) ++
  ((encodeLinearNe nq3Terms02 (-2) (4 : Fin 6)).filterMap normalize) ++
  ((encodeLinearNe nq3Terms12 (-1) (5 : Fin 6)).filterMap normalize) ++
  ((encodeAllDifferent nq3Vars [1, 2, 3]).filterMap normalize)

/-! ### Corpus bridges -/

/-- **Bridge.** The columns `alldifferent (Vector.ofFn id)` constraint makes the
    three row values pairwise distinct (reuses `alldifferent_sat`). -/
theorem nq3_cols_sat (a : HomogeneousAssignment 3)
    (h : HomogeneousCSP.satisfiesConstraint (alldifferent nq3Scope) a) :
    (nq3Vars.map a).Nodup :=
  alldifferent_sat nq3Scope a h

/-- **Bridge.** The positive-diagonal `alldifferent_diag_pos 3` constraint
    (`Nodup [a 0, a 1 + 1, a 2 + 2]`) makes the three positive diagonals pairwise
    distinct. -/
theorem nq3_diag_pos_sat (a : HomogeneousAssignment 3)
    (h : HomogeneousCSP.satisfiesConstraint (alldifferent_diag_pos 3) a) :
    a (0 : Fin 3) ≠ a (1 : Fin 3) + 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) + 2 ∧
      a (1 : Fin 3) + 1 ≠ a (2 : Fin 3) + 2 := by
  simp only [HomogeneousCSP.satisfiesConstraint, alldifferent_diag_pos,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    CSP.map_assignment, vget, decide_eq_true_eq,
    List.ofFn_succ, List.ofFn_zero, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, or_false, and_true, not_false_eq_true, not_or,
    Fin.val_succ, Fin.val_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_add, add_zero] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **Bridge.** The negative-diagonal `alldifferent_diag_neg 3` constraint
    (`Nodup [a 0, a 1 - 1, a 2 - 2]`) makes the three negative diagonals pairwise
    distinct. -/
theorem nq3_diag_neg_sat (a : HomogeneousAssignment 3)
    (h : HomogeneousCSP.satisfiesConstraint (alldifferent_diag_neg 3) a) :
    a (0 : Fin 3) ≠ a (1 : Fin 3) - 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) - 2 ∧
      a (1 : Fin 3) - 1 ≠ a (2 : Fin 3) - 2 := by
  simp only [HomogeneousCSP.satisfiesConstraint, alldifferent_diag_neg,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    CSP.map_assignment, vget, decide_eq_true_eq,
    List.ofFn_succ, List.ofFn_zero, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, List.nodup_nil, or_false, and_true, not_false_eq_true, not_or,
    Fin.val_succ, Fin.val_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_add, sub_zero] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ### The PB certificate -/

/-- The veripb-elaborated kernel proof of UNSAT for `nq3User`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The six thresholds `a i ≤ 1`,
    `a i ≤ 2` map to OPB `x1..x6`; the six diagonal selectors to `x7..x12`. -/
def nq3KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 18;
rup >= 0 : ~ ;
pol 4 s;
pol 5 s;
pol 6 s;
pol 7 s;
rup 1 ~x8 >= 1 : ~ 23;
pol 8 s;
pol 9 s;
pol 10 s;
pol 11 s;
pol 12 s;
rup 1 x11 >= 1 : ~ 29;
pol 13 30 9 * +;
pol 14 s;
pol 15 s;
pbc 1000000000000000 x4 1000000000000000 x3 1000000000000000 ~x6 1000000000000000 ~x5 2000000000000000 x9 2000000000000000 x12 >= 4000000000000000 : subproof
pol 34 32 1000000000000000 * + 2000000000000000 d;
pol 34 35 2000000000000000 * + 25 1000000000000000 * +;
qed : 36;
pbc 1000000000000000 x4 1000000000000000 x3 1000000000000000 ~x6 1000000000000000 ~x5 2000000000000000 x9 2000000000000000 x12 >= 4000000000000000 : subproof
pol 38 25 1000000000000000 * + 2000000000000000 d;
pol 38 39 2000000000000000 * + 32 1000000000000000 * +;
qed : 40;
pbc 500000000000000 x9 1000000000000000 x10 >= 500000000000000 : subproof
pol 42 25 500000000000000 * + 27 500000000000000 * + 31 500000000000000 * + 500000000000000 d;
pol 42 43 500000000000000 * +;
qed : 44;
pbc 500000000000000 x9 1000000000000000 x10 >= 500000000000000 : subproof
pol 46 25 500000000000000 * + 27 500000000000000 * + 31 500000000000000 * + 500000000000000 d;
pol 46 47 500000000000000 * +;
qed : 48;
pbc 499999999999998 ~x2 1 ~x1 1 x4 499999999999999 x3 2 x6 500000000000000 x5 500000000000001 x9 >= 500000000000001 : subproof
pol 50 31 500000000000000 * + 17 499999999999999 * + x6 + 500000000000001 d;
pol 50 51 999999999999999 * + 25 499999999999999 * + 18 500000000000001 * +;
qed : 52;
pbc 499999999999998 ~x2 1 ~x1 1 x4 499999999999999 x3 2 x6 500000000000000 x5 500000000000001 x9 >= 500000000000001 : subproof
pol 54 25 499999999999999 * + 18 500000000000001 * + ~x1 + 999999999999999 d;
pol 54 55 500000000000001 * + 31 500000000000000 * + 17 499999999999999 * +;
qed : 56;
pbc 333333333333333 ~x2 333333333333333 x3 333333333333333 x5 333333333333333 x9 >= 333333333333333 : subproof
pol 58 17 333333333333333 * + 333333333333333 d;
pol 58 59 666666666666667 * + 25 333333333333333 * + 31 666666666666666 * + 18 333333333333334 * +;
qed : 60;
pbc 333333333333333 ~x2 333333333333333 x3 333333333333333 x5 333333333333333 x9 >= 333333333333333 : subproof
pol 62 25 333333333333333 * + 31 666666666666666 * + 17 666666666666667 * + 18 333333333333334 * + ~x1 + 666666666666667 d;
pol 62 63 333333333333333 * +;
qed : 64;
pbc 333333333333333 x4 333333333333333 x3 333333333333333 x6 333333333333333 ~x5 666666666666666 x9 >= 999999999999999 : subproof
rup 1 x5 666666666666666 x9 >= 0 : ~ ;
pol 66 3 1000000000000000 * + 31 333333333333333 * + 17 333333333333333 * + 18 666666666666666 * + 67 + 1333333333333334 d;
pol 66 68 666666666666666 * + 25 333333333333333 * +;
qed : 69;
pbc 333333333333333 x4 333333333333333 x3 333333333333333 x6 333333333333333 ~x5 666666666666666 x9 >= 999999999999999 : subproof
pol 71 25 333333333333333 * + 666666666666666 d;
pol 71 72 1333333333333334 * + 3 1000000000000000 * + 31 333333333333333 * + 17 333333333333333 * + 18 666666666666666 * +;
qed : 73;
pbc 333333333333333 x4 333333333333333 x3 333333333333333 x6 333333333333333 ~x5 666666666666666 x9 >= 999999999999999 : subproof
rup 1 x5 666666666666666 x9 >= 0 : ~ ;
pol 75 3 1000000000000000 * + 31 333333333333333 * + 17 333333333333333 * + 18 666666666666666 * + 76 + 1333333333333334 d;
pol 75 77 666666666666666 * + 25 333333333333333 * +;
qed : 78;
pbc 333333333333333 x4 333333333333333 x3 333333333333333 x6 333333333333333 ~x5 666666666666666 x9 >= 999999999999999 : subproof
pol 80 25 333333333333333 * + 666666666666666 d;
pol 80 81 1333333333333334 * + 3 1000000000000000 * + 31 333333333333333 * + 17 333333333333333 * + 18 666666666666666 * +;
qed : 82;
pbc 249999999999999 x4 249999999999999 x3 249999999999999 x6 249999999999999 ~x5 499999999999998 x9 >= 749999999999997 : subproof
pol 84 25 249999999999999 * + 499999999999998 d;
pol 84 85 1000000000000002 * + 3 749999999999999 * + 31 249999999999999 * + 17 249999999999999 * + 18 500000000000000 * +;
qed : 86;
pbc 249999999999999 x4 249999999999999 x3 249999999999999 x6 249999999999999 ~x5 499999999999998 x9 >= 749999999999997 : subproof
rup 2 ~x2 2 ~x4 2 x5 499999999999998 x9 >= 0 : ~ ;
pol 88 3 749999999999999 * + 31 249999999999999 * + 17 249999999999999 * + 18 500000000000000 * + 89 + 1000000000000002 d;
pol 88 90 499999999999998 * + 25 249999999999999 * +;
qed : 91;
pbc 333333333333333 ~x2 333333333333333 x3 1 x6 333333333333333 x5 333333333333333 x9 >= 333333333333333 : subproof
pol 93 25 333333333333333 * + 31 666666666666666 * + 17 666666666666666 * + 18 333333333333334 * + ~x4 + 666666666666667 d;
pol 93 94 333333333333333 * +;
qed : 95;
pbc 333333333333333 ~x2 333333333333333 x3 1 x6 333333333333333 x5 333333333333333 x9 >= 333333333333333 : subproof
pol 97 x6 + 333333333333333 d;
pol 97 98 666666666666667 * + 25 333333333333333 * + 31 666666666666666 * + 17 666666666666666 * + 18 333333333333334 * +;
qed : 99;
pbc 1000000000000000 x9 1000000000000000 x10 >= 1000000000000000 : subproof
pol 101 25 1000000000000000 * + 27 1000000000000000 * + 31 1000000000000000 * + 3000000000000000 d;
pol 101 102 1000000000000000 * +;
qed : 103;
pbc 1000000000000000 x9 1000000000000000 x10 >= 1000000000000000 : subproof
pol 105 1000000000000000 d;
pol 105 106 3000000000000000 * + 25 1000000000000000 * + 27 1000000000000000 * + 31 1000000000000000 * +;
qed : 107;
pol 37 ~x9 0 * + ~x3 0 * + ~x4 0 * + ~x5 0 * + ~x6 0 * + ~x12 0 * + 4 d 250000000000000 d;
pol 37 ~x9 0 * + ~x3 0 * + ~x4 0 * + ~x5 0 * + ~x6 0 * + ~x12 0 * + 4 d 250000000000000 d;
rup 1 x4 1 x3 1 ~x6 >= 0 : ~;
pol 25 27 + 31 + s 26 111 + 4 d + 28 ~x4 + 2 d + 16 + s 1 + s;
rup 1 x10 >= 1 : ~ 112 27;
rup 1 x1 2 x10 >= 2 : ~ 113;
pol 3 17 + 112 + 28 114 + + s;
rup 1 x2 1 ~x4 >= 0 : ~;
pol 18 20 112 + + 115 2 * + 21 x1 + s 116 + 3 d 2 * + s ~x6 + s;
rup 1 x4 >= 1 : ~ 117 2;
rup 1 ~x9 >= 1 : ~ 117 118 26;
rup 1 ~x5 >= 1 : ~ 117 16;
rup 1 x7 >= 1 : ~ 112 117 118 20;
rup 1 ~x12 >= 1 : ~ 117 118 120 33;
rup 1 ~x2 >= 1 : ~ 121 21;
rup 1 ~x6 >= 1 : ~ 122 32;
rup 1 ~x2 1 ~x4 1 ~x6 >= 2 : 123 124 ~;
pol 18 125 +;
output NONE ;
conclusion UNSAT : 126;
end pseudo-Boolean proof;
"

/-- The PB encoding of `nqueens_csp 3` is unsatisfiable — established by the
    external PB certificate, kernel-checked through PBLean's verified reflection
    checker (`native_decide` runs the checker; RoundingSat / veripb / the
    serializer are untrusted). -/
theorem nq3_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((nq3Sig.monotonicity ++ nq3User).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 12 nq3KernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain row assignment placing three queens
    non-attacking (distinct rows, distinct positive diagonals, distinct negative
    diagonals). -/
theorem nq3_no_sol : ¬ ∃ (a : Fin nq3Sig.nInt → Int) (_ : Fin nq3Sig.nBool → Bool),
    (∀ i, a i ∈ nq3Sig.values i) ∧
    ((nq3Vars.map a).Nodup ∧
     (a (0 : Fin 3) ≠ a (1 : Fin 3) + 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) + 2 ∧
        a (1 : Fin 3) + 1 ≠ a (2 : Fin 3) + 2) ∧
     (a (0 : Fin 3) ≠ a (1 : Fin 3) - 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) - 2 ∧
        a (1 : Fin 3) - 1 ≠ a (2 : Fin 3) - 2)) := by
  apply csp_unsat_generic nq3Sig nq3User
    (fun a _ => (nq3Vars.map a).Nodup ∧
      (a (0 : Fin 3) ≠ a (1 : Fin 3) + 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) + 2 ∧
        a (1 : Fin 3) + 1 ≠ a (2 : Fin 3) + 2) ∧
      (a (0 : Fin 3) ≠ a (1 : Fin 3) - 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) - 2 ∧
        a (1 : Fin 3) - 1 ≠ a (2 : Fin 3) - 2))
    nq3Aux
  · intro a bA hdom hP c hc
    obtain ⟨hND, ⟨hP01, hP02, hP12⟩, ⟨hN01, hN02, hN12⟩⟩ := hP
    simp only [nq3User, List.mem_append] at hc
    rcases hc with ((((((hc | hc) | hc) | hc) | hc) | hc) | hc)
    · refine extend_sat_encodeLinearNe a bA (nq3Aux a bA) hdom nq3Terms01 1 (0 : Fin 6) ?_ rfl c hc
      rw [nq3Sum01]; omega
    · refine extend_sat_encodeLinearNe a bA (nq3Aux a bA) hdom nq3Terms02 2 (1 : Fin 6) ?_ rfl c hc
      rw [nq3Sum02]; omega
    · refine extend_sat_encodeLinearNe a bA (nq3Aux a bA) hdom nq3Terms12 1 (2 : Fin 6) ?_ rfl c hc
      rw [nq3Sum12]; omega
    · refine extend_sat_encodeLinearNe a bA (nq3Aux a bA) hdom nq3Terms01 (-1) (3 : Fin 6) ?_ rfl c hc
      rw [nq3Sum01]; omega
    · refine extend_sat_encodeLinearNe a bA (nq3Aux a bA) hdom nq3Terms02 (-2) (4 : Fin 6) ?_ rfl c hc
      rw [nq3Sum02]; omega
    · refine extend_sat_encodeLinearNe a bA (nq3Aux a bA) hdom nq3Terms12 (-1) (5 : Fin 6) ?_ rfl c hc
      rw [nq3Sum12]; omega
    · exact extend_sat_encodeAllDifferent a bA (nq3Aux a bA) hdom nq3Vars [1, 2, 3] c hc hND
  · exact nq3_formulaUnsat

/-- **End-to-end N-Queens UNSAT (3×3).** The corpus CSP `nqueens_csp 3` — place
    three queens on a 3×3 board with no shared row, column, or diagonal — is
    unsatisfiable, discharged through the verified PB pipeline: the columns
    `alldifferent` and the two three-element diagonal bridges turn any solution
    into pairwise-distinct rows and six diagonal `≠` facts, the generic spine
    `csp_unsat_generic` turns those into a PB model (columns via aux-free
    `encodeAllDifferent`, diagonals via Big-M `encodeLinearNe`), and the committed
    certificate `nq3_formulaUnsat` contradicts it. -/
theorem nqueens_3_unsat : ¬ (nqueens_csp 3).isSatisfiable := by
  rintro ⟨a, hsol⟩
  have hdom : ∀ i : Fin nq3Sig.nInt, a i ∈ nq3Sig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (3 : ℕ)) a := by
      apply hsol
      show bound i 1 (3 : ℕ) ∈ queens_bounds 3 ++
        [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 3, alldifferent_diag_neg 3]
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 1 (3 : ℕ) a hb
    have h2' : a i ≤ 3 := by exact_mod_cast h2
    show a i ∈ domainValues 1 3
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  have hNodup : (nq3Vars.map a).Nodup := by
    refine nq3_cols_sat a (hsol _ ?_)
    show alldifferent nq3Scope ∈ queens_bounds 3 ++
      [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 3, alldifferent_diag_neg 3]
    apply List.mem_append_right; exact List.mem_cons_self
  have hDiagP : a (0 : Fin 3) ≠ a (1 : Fin 3) + 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) + 2 ∧
      a (1 : Fin 3) + 1 ≠ a (2 : Fin 3) + 2 := by
    refine nq3_diag_pos_sat a (hsol _ ?_)
    show alldifferent_diag_pos 3 ∈ queens_bounds 3 ++
      [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 3, alldifferent_diag_neg 3]
    apply List.mem_append_right; exact List.mem_cons_of_mem _ List.mem_cons_self
  have hDiagN : a (0 : Fin 3) ≠ a (1 : Fin 3) - 1 ∧ a (0 : Fin 3) ≠ a (2 : Fin 3) - 2 ∧
      a (1 : Fin 3) - 1 ≠ a (2 : Fin 3) - 2 := by
    refine nq3_diag_neg_sat a (hsol _ ?_)
    show alldifferent_diag_neg 3 ∈ queens_bounds 3 ++
      [alldifferent (_root_.Vector.ofFn id), alldifferent_diag_pos 3, alldifferent_diag_neg 3]
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact nq3_no_sol ⟨a, fun _ => false, hdom, hNodup, hDiagP, hDiagN⟩

end CSP.L2S.PB.NQueens
