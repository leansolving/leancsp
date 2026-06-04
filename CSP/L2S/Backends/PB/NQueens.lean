import CSP.L2S.Backends.PB.LinearNe
import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Tests.lean.«08_queens»

namespace CSP.L2S.PB.NQueens

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for `nqueens_csp 2`

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

end CSP.L2S.PB.NQueens
