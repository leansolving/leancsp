import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.NotAllEqual
import CSP.L2S.Backends.PB.AllDifferent

namespace CSP.L2S.PB

open CSP.L2S

/-!
# PB backend — bridges for the not-all-equal / `ne` / `ne_const` patterns

The not-all-equal encoders are aux-free, so they ride the generic spine
`csp_unsat_generic` through reusable bridges, the analogues of `bound_sat` /
`extend_sat_encodeLinearLe`:

* `schur_triple_sat` — a satisfied `schur_triple` makes the three assigned values
  not all equal;
* `extend_sat_encodeNotAllEqualBin` / `..Multi` — a normalized not-all-equal
  constraint is modelled by `extend a bA auxA` whenever two recovered values
  differ (the binary and `k > 2`-valued forms);
* `not_equal_sat` and `not_equals_const_sat` / `extend_sat_encodeNeConst` — the
  explicit-edge and forbidden-colour patterns.
-/

/-- **Bridge.** A satisfied corpus `schur_triple v1 v2 v3` constraint makes the
    three assigned values not all equal.  Mirrors `bound_sat` / `alldifferent_sat`. -/
theorem schur_triple_sat {n : ℕ} (v1 v2 v3 : VarType n)
    (a : IntAssignment n)
    (h : IntCSP.satisfiesConstraintInt (schur_triple v1 v2 v3) a) :
    a v1 ≠ a v2 ∨ a v1 ≠ a v3 ∨ a v2 ≠ a v3 := by
  simp only [IntCSP.satisfiesConstraintInt, schur_triple, patternHolds, valAt_eq] at h
  exact h

/-- **Bridge.** A satisfied corpus `not_equal v1 v2` constraint (graph-colouring
    edge, pattern `ne`) makes the two assigned values differ.  Mirrors
    `schur_triple_sat`; the binary checker `binary_dynamic_constraint` reduces the
    same way once `binary_constraint` is unfolded. -/
theorem not_equal_sat {n : ℕ} (v1 v2 : VarType n)
    (a : IntAssignment n)
    (h : IntCSP.satisfiesConstraintInt (not_equal v1 v2) a) :
    a v1 ≠ a v2 := by
  simp only [IntCSP.satisfiesConstraintInt, not_equal, patternHolds, valAt_eq] at h
  exact h

/-- **Bridge.** A satisfied corpus `not_equals_const v c` constraint (forbidden
    colour, pattern `ne_const`) makes the assigned value differ from `c`.  Mirrors
    `bound_sat`; the unary checker reduces once `unary_constraint` is unfolded. -/
theorem not_equals_const_sat {n : ℕ} (v : VarType n) (c : ℤ)
    (a : IntAssignment n)
    (h : IntCSP.satisfiesConstraintInt (not_equals_const v c) a) :
    a v ≠ c := by
  simp only [IntCSP.satisfiesConstraintInt, not_equals_const, patternHolds, valAt_eq] at h
  exact h

/-- **Bridge.** A satisfied `equals_const v c` constraint (a fixed value, e.g. a
    Sudoku given) pins the assigned value to `c`.  The positive twin of
    `not_equals_const_sat`. -/
theorem equals_const_sat {n : ℕ} (v : VarType n) (c : ℤ)
    (a : IntAssignment n)
    (h : IntCSP.satisfiesConstraintInt (equals_const v c) a) :
    a v = c := by
  simp only [IntCSP.satisfiesConstraintInt, equals_const, patternHolds, valAt_eq] at h
  exact h

/-- **Bridge.** A normalized `encodeNeConst j val` constraint is modelled by
    `extend a bA auxA` whenever the recovered value of `xⱼ` differs from `val`. -/
theorem extend_sat_encodeNeConst {S : CSPSig} (a : Fin S.nInt → Int)
    (bA : Fin S.nBool → Bool) (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (j : Fin S.nInt) (val : Int) (hne : a j ≠ val)
    (c' : PBConstr (PBVar S)) (hc : normalize (encodeNeConst j val) = some c') :
    c'.sat (extend a bA auxA) := by
  rw [← normalize_sat_iff _ _ hc]
  refine encodeNeConst_sound (extend a bA auxA) (extend_orderConsistent a bA auxA) j val ?_
  rw [extend_intValue a bA auxA hdom j]
  exact hne

/-- **Bridge.** A normalized `encodeNotAllEqualBin` constraint is modelled by
    `extend a bA auxA` whenever two of the recovered values differ. -/
theorem extend_sat_encodeNotAllEqualBin {S : CSPSig} (a : Fin S.nInt → Int)
    (bA : Fin S.nBool → Bool) (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (vars : List (Fin S.nInt)) (hw : ∀ i ∈ vars, 0 < S.width i)
    (c0 c1 : Int) (hdomvals : ∀ i ∈ vars, S.values i = [c0, c1])
    (hne : ∃ i ∈ vars, ∃ i' ∈ vars, a i ≠ a i')
    (c' : PBConstr (PBVar S))
    (hc : c' ∈ (encodeNotAllEqualBin vars hw).filterMap normalize) :
    c'.sat (extend a bA auxA) := by
  rw [List.mem_filterMap] at hc
  obtain ⟨sc, hsc_mem, hnorm⟩ := hc
  rw [← normalize_sat_iff _ _ hnorm]
  refine encodeNotAllEqualBin_sound (extend a bA auxA) vars c0 c1 hw hdomvals ?_ sc hsc_mem
  obtain ⟨i, hi, i', hi', hii⟩ := hne
  refine ⟨i, hi, i', hi', ?_⟩
  rw [extend_intValue a bA auxA hdom i, extend_intValue a bA auxA hdom i']
  exact hii

/-- **Bridge (multi-valued).** The `k > 2`-valued analogue of
    `extend_sat_encodeNotAllEqualBin`. -/
theorem extend_sat_encodeNotAllEqualMulti {S : CSPSig} (a : Fin S.nInt → Int)
    (bA : Fin S.nBool → Bool) (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (vars : List (Fin S.nInt)) (D : List Int)
    (hne : ∃ i ∈ vars, ∃ i' ∈ vars, a i ≠ a i')
    (c' : PBConstr (PBVar S))
    (hc : c' ∈ (encodeNotAllEqualMulti vars D).filterMap normalize) :
    c'.sat (extend a bA auxA) := by
  rw [List.mem_filterMap] at hc
  obtain ⟨sc, hsc_mem, hnorm⟩ := hc
  rw [← normalize_sat_iff _ _ hnorm]
  refine encodeNotAllEqualMulti_sound (extend a bA auxA) (extend_orderConsistent a bA auxA)
    vars D ?_ sc hsc_mem
  obtain ⟨i, hi, i', hi', hii⟩ := hne
  refine ⟨i, hi, i', hi', ?_⟩
  rw [extend_intValue a bA auxA hdom i, extend_intValue a bA auxA hdom i']
  exact hii

/-- **Bridge.** A satisfied `alldifferent scope` constraint makes the assigned values
    along the scope pairwise distinct (`Nodup`).  Mirrors `bound_sat` / `linear_le_sat`. -/
theorem alldifferent_sat {n m : ℕ} (scope : _root_.Vector (VarType n) m)
    (a : IntAssignment n)
    (h : IntCSP.satisfiesConstraintInt (alldifferent scope) a) :
    (scope.toList.map a).Nodup := by
  simp only [IntCSP.satisfiesConstraintInt, alldifferent, patternHolds, map_valAt] at h
  exact h

/-- **Bridge.** A normalized `encodeAllDifferent` constraint is modelled by
    `extend a bA auxA` (`alldifferent` is aux-free) whenever the recovered values are
    pairwise distinct.  Composes `encodeAllDifferent_sound` with `extend_intValue`. -/
theorem extend_sat_encodeAllDifferent {S : CSPSig} (a : Fin S.nInt → Int)
    (bA : Fin S.nBool → Bool) (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (vars : List (Fin S.nInt)) (D : List Int) (c' : PBConstr (PBVar S))
    (hc : c' ∈ (encodeAllDifferent vars D).filterMap normalize)
    (hnodup : (vars.map a).Nodup) :
    c'.sat (extend a bA auxA) := by
  rw [List.mem_filterMap] at hc
  obtain ⟨sc, hsc_mem, hnorm⟩ := hc
  rw [← normalize_sat_iff _ _ hnorm]
  have hmap : vars.map (extend a bA auxA).intValue = vars.map a :=
    List.map_congr_left (fun i _ => extend_intValue a bA auxA hdom i)
  exact encodeAllDifferent_sound (extend a bA auxA) (extend_orderConsistent a bA auxA)
    vars D (by rw [hmap]; exact hnodup) sc hsc_mem

end CSP.L2S.PB
