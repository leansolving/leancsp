import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Backends.PB.Adapter

/-!
# Pattern-satisfaction bridges for the Proofs/ corpus

Two-way (`iff`) bridges from `IntCSP.satisfiesConstraintInt` (= `patternHolds`)
to the direct `Fin`-indexed forms the equivalence and symmetry-breaking proofs
reason with.  The forward-only `*_sat` lemmas in `Backends/PB/` serve the UNSAT
pipeline; the symmetry proofs need both directions because they transport
solutions across permutations.

All scope-level `valAt`/dite plumbing is concentrated here: a constraint wrapper
stores `Fin.val`-projected indices, so `valAt` always hits its in-range branch
(`valAt_eq` / `map_valAt` from `Backends/PB/Adapter.lean`).
-/

namespace CSP.L2S

open CSP.L2S.PB

/-- A `Vector.ofFn` scope, evaluated through an assignment, is the `List.ofFn`
    of the composite. -/
theorem toList_map_ofFn {n m : ℕ} (a : IntAssignment n) (f : Fin m → Fin n) :
    ((_root_.Vector.ofFn f).toList.map a) = List.ofFn (a ∘ f) := by
  simp [_root_.Vector.toList_ofFn, List.map_ofFn]

/-- `alldifferent` over a vector scope means the assigned values are `Nodup`. -/
theorem alldifferent_holds_iff {num_vars k : ℕ}
    (scope : _root_.Vector (VarType num_vars) k) (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (alldifferent scope) a ↔
    (scope.toList.map a).Nodup := by
  simp only [IntCSP.satisfiesConstraintInt, alldifferent, patternHolds, map_valAt]

/-- `alldifferent_all` means the whole assignment is `Nodup`. -/
theorem alldifferent_all_holds_iff {n : ℕ} (a : IntAssignment n) :
    IntCSP.satisfiesConstraintInt (alldifferent_all n) a ↔
    (List.ofFn a).Nodup := by
  rw [alldifferent_all, alldifferent_holds_iff, toList_map_ofFn, Function.comp_id]

/-- `increasing` over a vector scope means the assigned values are pairwise `≤`. -/
theorem increasing_holds_iff {num_vars k : ℕ}
    (scope : _root_.Vector (VarType num_vars) k) (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (increasing scope) a ↔
    List.Pairwise (· ≤ ·) (scope.toList.map a) := by
  simp only [IntCSP.satisfiesConstraintInt, increasing, patternHolds, map_valAt]

/-- `sum_eq` over a vector scope means the assigned values sum to the target. -/
theorem sum_eq_holds_iff {num_vars k : ℕ}
    (scope : _root_.Vector (VarType num_vars) k) (t : ℤ) (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (sum_eq scope t) a ↔
    (scope.toList.map a).sum = t := by
  simp only [IntCSP.satisfiesConstraintInt, sum_eq, sum_rel, patternHolds, relHolds,
    map_valAt]

/-- `sum_le` over a vector scope bounds the sum of the assigned values. -/
theorem sum_le_holds_iff {num_vars k : ℕ}
    (scope : _root_.Vector (VarType num_vars) k) (t : ℤ) (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (sum_le scope t) a ↔
    (scope.toList.map a).sum ≤ t := by
  simp only [IntCSP.satisfiesConstraintInt, sum_le, sum_rel, patternHolds, relHolds,
    map_valAt]

/-- `bound` pins the assigned value into `[lb, ub]`. -/
theorem bound_holds_iff {num_vars : ℕ} (v : VarType num_vars) (lb ub : ℤ)
    (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (bound v lb ub) a ↔ lb ≤ a v ∧ a v ≤ ub := by
  simp only [IntCSP.satisfiesConstraintInt, bound, patternHolds, valAt_eq]

/-- `not_equal` means the two assigned values differ. -/
theorem not_equal_holds_iff {num_vars : ℕ} (v1 v2 : VarType num_vars)
    (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (not_equal v1 v2) a ↔ a v1 ≠ a v2 := by
  simp only [IntCSP.satisfiesConstraintInt, not_equal, patternHolds, valAt_eq]

/-- `equals_const` means the assigned value is the constant. -/
theorem equals_const_holds_iff {num_vars : ℕ} (v : VarType num_vars) (c : ℤ)
    (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (equals_const v c) a ↔ a v = c := by
  simp only [IntCSP.satisfiesConstraintInt, equals_const, patternHolds, valAt_eq]

/-- `less_than_const` means the assigned value is below the constant. -/
theorem less_than_const_holds_iff {num_vars : ℕ} (v : VarType num_vars) (c : ℤ)
    (a : IntAssignment num_vars) :
    IntCSP.satisfiesConstraintInt (less_than_const v c) a ↔ a v < c := by
  simp only [IntCSP.satisfiesConstraintInt, less_than_const, patternHolds, valAt_eq]

/-- The N-Queens positive diagonal: `x[i] + i` all different. -/
theorem diag_pos_holds_iff {n : ℕ} (a : IntAssignment n) :
    IntCSP.satisfiesConstraintInt (alldifferent_diag_pos n) a ↔
    (List.ofFn fun i : Fin n => a i + (i.val : ℤ)).Nodup := by
  have h : ((List.range n).zip ((List.range n).map Int.ofNat)).map
        (fun p => valAt a p.1 + p.2) = List.ofFn fun i : Fin n => a i + (i.val : ℤ) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hin : i < n := by simpa using h2
      simp [valAt, hin]
  simp only [IntCSP.satisfiesConstraintInt, alldifferent_diag_pos, patternHolds, h]

/-- The N-Queens negative diagonal: `x[i] - i` all different. -/
theorem diag_neg_holds_iff {n : ℕ} (a : IntAssignment n) :
    IntCSP.satisfiesConstraintInt (alldifferent_diag_neg n) a ↔
    (List.ofFn fun i : Fin n => a i - (i.val : ℤ)).Nodup := by
  have h : ((List.range n).zip ((List.range n).map fun i => -(Int.ofNat i))).map
        (fun p => valAt a p.1 + p.2) = List.ofFn fun i : Fin n => a i - (i.val : ℤ) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      have hin : i < n := by simpa using h2
      simp [valAt, hin]
      ring
  simp only [IntCSP.satisfiesConstraintInt, alldifferent_diag_neg, patternHolds, h]

end CSP.L2S
