import CSP.L2S.Backends.PB.Extend
import CSP.L2S.Core
import CSP.L2S.Constraints

namespace CSP.L2S.PB

open CSP.L2S
open scoped BigOperators

/-!
# PB backend — `HomogeneousCSP` → `CSPSig` adapter (PLAN.md M5)

The generic spine (`Extend.lean`) proves `formulaUnsat → ¬∃ in-domain linear
solution` over an abstract `CSPSig` and a list of linear `≤` constraints.  This
file connects it to a real `HomogeneousCSP`:

* `domainValues lb ub` turns a `bound` interval into the strictly-sorted value
  list a `CSPSig` needs; `toCSPSig` builds the signature (one integer variable
  per CSP variable, `nBool = nAux = 0`);
* per-pattern *bridge* lemmas turn `HomogeneousCSP.satisfiesConstraint` of a
  `bound` / `linear_le` into the in-domain / linear-`≤` facts the spine consumes;
* `unsat_of_pb` composes them into a `¬ csp.isSatisfiable` theorem.

Phase 1 covers `bound` + `linear_le` (a `≥` constraint is just `linear_le` with
negated coefficients); wider pattern coverage rides on the M4 encoders.
-/

/-! ### Domain value lists -/

/-- The integer interval `[lb, ub]` as a strictly-increasing list. -/
def domainValues (lb ub : ℤ) : List ℤ :=
  (List.range (ub + 1 - lb).toNat).map (fun k : ℕ => lb + (k : ℤ))

theorem domainValues_sorted (lb ub : ℤ) : (domainValues lb ub).Pairwise (· < ·) := by
  unfold domainValues
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_range]
  omega

theorem domainValues_nonempty {lb ub : ℤ} (h : lb ≤ ub) : 0 < (domainValues lb ub).length := by
  simp only [domainValues, List.length_map, List.length_range]
  omega

theorem mem_domainValues {lb ub x : ℤ} : x ∈ domainValues lb ub ↔ lb ≤ x ∧ x ≤ ub := by
  simp only [domainValues, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨(x - lb).toNat, by omega, by omega⟩

/-! ### The signature -/

/-- Build a `CSPSig` from a `HomogeneousCSP` and per-variable bounds: one integer
    variable per CSP variable, each with domain `[lb i, ub i]`. -/
def toCSPSig (csp : HomogeneousCSP) (lb ub : Fin csp.num_vars → ℤ)
    (hle : ∀ i, lb i ≤ ub i) : CSPSig where
  nInt := csp.num_vars
  nBool := 0
  nAux := 0
  values := fun i => domainValues (lb i) (ub i)
  sorted := fun i => domainValues_sorted (lb i) (ub i)
  nonempty := fun i => domainValues_nonempty (hle i)

/-! ### Bridge: `bound` satisfaction ⇒ in-range -/

/-- A satisfied `bound v lb ub` constraint pins `a v` to the interval `[lb, ub]`. -/
theorem bound_sat {n : ℕ} (v : Fin n) (lb ub : ℤ) (a : HomogeneousAssignment n)
    (h : HomogeneousCSP.satisfiesConstraint (bound v lb ub) a) : lb ≤ a v ∧ a v ≤ ub := by
  simp only [HomogeneousCSP.satisfiesConstraint, bound, CSP.satisfies_dynamic_constraint,
    CSP.satisfies_constraint, CSP.sat, extractValues, CSP.map_assignment, List.ofFn_succ,
    List.ofFn_zero, _root_.Vector.get, decide_eq_true_eq] at h
  exact h

/-! ### Bridge: `linear_le` satisfaction ⇒ the spine's linear `≤` -/

/-- `extractValues (map_assignment a scope) = scope.toList.map a`. -/
theorem extractValues_map_assignment {n m : ℕ} (a : HomogeneousAssignment n)
    (scope : _root_.Vector (HomogeneousVarIndex n) m) :
    extractValues (map_assignment a scope) = scope.toList.map a := by
  unfold extractValues map_assignment
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_ofFn, List.getElem_map]
    congr 1

/-- A satisfied `linear_le scope coeffs target` constraint gives the spine's
    linear-`≤` fact over `terms = coeffs.zip scope`. -/
theorem linear_le_sat {n m : ℕ} (scope : _root_.Vector (HomogeneousVarIndex n) m)
    (coeffs : _root_.Vector ℤ m) (target : ℤ) (a : HomogeneousAssignment n)
    (h : HomogeneousCSP.satisfiesConstraint (linear_le scope coeffs target) a) :
    (((coeffs.toList.zip scope.toList)).map (fun p => p.1 * a p.2)).sum ≤ target := by
  simp only [HomogeneousCSP.satisfiesConstraint, linear_le, linear_rel,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    decide_eq_true_eq] at h
  rw [extractValues_map_assignment, List.zipWith_map_right] at h
  -- h : (List.zipWith (fun c sv => c * a sv) coeffs.toList scope.toList).sum ≤ target
  rw [List.map_zip_eq_zipWith]
  exact h

/-! ### The generic `HomogeneousCSP` UNSAT theorem -/

/-- **HomogeneousCSP UNSAT bridge.** If every variable `i` has its `bound (lb i) (ub i)`
    constraint in the CSP, the linear `≤` facts `lin` follow from any solution, and the
    PB order encoding of `(toCSPSig …, lin)` is `formulaUnsat`, then the CSP is unsatisfiable. -/
theorem unsat_of_pb (csp : HomogeneousCSP) (lb ub : Fin csp.num_vars → ℤ)
    (hle : ∀ i, lb i ≤ ub i)
    (hbound : ∀ i, bound i (lb i) (ub i) ∈ csp.constraints)
    (lin : List (List (Int × Fin csp.num_vars) × Int))
    (hlin : ∀ a, csp.isSolution a → ∀ c ∈ lin, (c.1.map (fun p => p.1 * a p.2)).sum ≤ c.2)
    (hunsat : VeriPB.Reflect.formulaUnsat
        ((encodeLinear (toCSPSig csp lb ub hle) lin).toArray.map PBConstr.toNatConstr)) :
    ¬ csp.isSatisfiable := by
  rintro ⟨a, hsol⟩
  refine csp_unsat_of_linear (toCSPSig csp lb ub hle) lin hunsat ⟨a, ?_, hlin a hsol⟩
  intro i
  show a i ∈ domainValues (lb i) (ub i)
  rw [mem_domainValues]
  exact bound_sat i (lb i) (ub i) a (hsol _ (hbound i))

end CSP.L2S.PB
