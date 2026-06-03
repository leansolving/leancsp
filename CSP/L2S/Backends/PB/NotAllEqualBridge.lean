import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.NotAllEqual
import CSP.L2S.Backends.PB.AllDifferent

namespace CSP.L2S.PB

open CSP.L2S

/-!
# PB backend — adapter bridges for the not-all-equal / `ne` / `ne_const` patterns

The not-all-equal encoder (`encodeNotAllEqualBin` + `encodeNotAllEqualBin_sound`,
`NotAllEqual.lean`) is aux-free, so — like `alldifferent` for pigeonhole — it
rides on the existing generic spine `csp_unsat_generic` (`Extend.lean`) through
two reusable bridges, the analogues of `bound_sat` / `extend_sat_encodeLinearLe`:

* `schur_triple_sat` — a satisfied corpus `schur_triple v1 v2 v3` constraint makes
  the three assigned values not all equal (`a v1 ≠ a v2 ∨ a v1 ≠ a v3 ∨ a v2 ≠ a v3`);
* `extend_sat_encodeNotAllEqualBin` — a normalized `encodeNotAllEqualBin` constraint
  is modelled by `extend a bA auxA` (it mentions only thresholds) whenever two of
  the recovered values differ; composes `encodeNotAllEqualBin_sound` with
  `extend_intValue`.

These power the end-to-end UNSAT proofs for the binary-domain colouring showcase
CSPs `vdw_2_3_9` (`VanDerWaerden.lean`), `ramsey_3_3_K6` (`Ramsey.lean`), and the
graph 2-colouring `k3_2col` (`GraphColoring.lean`).

The multi-valued (`k > 2`-colour) analogue `extend_sat_encodeNotAllEqualMulti`
mirrors `extend_sat_encodeNotAllEqualBin` but composes `encodeNotAllEqualMulti_sound`
(`AllDifferent.lean`, the per-value cardinality form) — it powers the end-to-end
3-colour Schur UNSAT proof `schur_3_14` (`Schur3.lean`).

Two further pattern bridges support graph colouring with explicit edges and
forbidden colours: `not_equal_sat` (`ne` edge → the endpoints differ) and
`not_equals_const_sat` / `extend_sat_encodeNeConst` (`ne_const` → the value avoids
the forbidden constant, modelled via the aux-free `encodeNeConst`).  These power
the forbidden-colour CSP `k2_forbidden` (`ForbiddenColoring.lean`), the first
end-to-end consumer of `encodeNeConst`.
-/

/-- **Bridge.** A satisfied corpus `schur_triple v1 v2 v3` constraint makes the
    three assigned values not all equal.  Mirrors `bound_sat` / `alldifferent_sat`. -/
theorem schur_triple_sat {n : ℕ} (v1 v2 v3 : HomogeneousVarIndex n)
    (a : HomogeneousAssignment n)
    (h : HomogeneousCSP.satisfiesConstraint (schur_triple v1 v2 v3) a) :
    a v1 ≠ a v2 ∨ a v1 ≠ a v3 ∨ a v2 ≠ a v3 := by
  simp only [HomogeneousCSP.satisfiesConstraint, schur_triple,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    extractValues, CSP.map_assignment, List.ofFn_succ, List.ofFn_zero,
    _root_.Vector.get, decide_eq_true_eq] at h
  exact h

/-- **Bridge.** A satisfied corpus `not_equal v1 v2` constraint (graph-colouring
    edge, pattern `ne`) makes the two assigned values differ.  Mirrors
    `schur_triple_sat`; the binary checker `binary_dynamic_constraint` reduces the
    same way once `binary_constraint` is unfolded. -/
theorem not_equal_sat {n : ℕ} (v1 v2 : HomogeneousVarIndex n)
    (a : HomogeneousAssignment n)
    (h : HomogeneousCSP.satisfiesConstraint (not_equal v1 v2) a) :
    a v1 ≠ a v2 := by
  simp only [HomogeneousCSP.satisfiesConstraint, not_equal,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    CSP.binary_dynamic_constraint, CSP.binary_constraint,
    CSP.map_assignment, _root_.Vector.get, decide_eq_true_eq] at h
  exact h

/-- **Bridge.** A satisfied corpus `not_equals_const v c` constraint (forbidden
    colour, pattern `ne_const`) makes the assigned value differ from `c`.  Mirrors
    `bound_sat`; the unary checker reduces once `unary_constraint` is unfolded. -/
theorem not_equals_const_sat {n : ℕ} (v : HomogeneousVarIndex n) (c : ℤ)
    (a : HomogeneousAssignment n)
    (h : HomogeneousCSP.satisfiesConstraint (not_equals_const v c) a) :
    a v ≠ c := by
  simp only [HomogeneousCSP.satisfiesConstraint, not_equals_const,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    CSP.unary_dynamic_constraint, CSP.unary_constraint,
    CSP.map_assignment, _root_.Vector.get, decide_eq_true_eq] at h
  exact h

/-- **Bridge.** A normalized `encodeNeConst j val` constraint (`xⱼ ≠ val`, aux-free)
    is modelled by `extend a bA auxA` whenever the recovered value of `xⱼ` differs
    from `val`.  Composes `encodeNeConst_sound` (needs `orderConsistent`, supplied by
    `extend_orderConsistent`) with `extend_intValue`. -/
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
    `extend a bA auxA` (for any Boolean / aux setting — it mentions only thresholds)
    whenever two of the recovered values differ.  Composes
    `encodeNotAllEqualBin_sound` with `extend_intValue`; the analogue of
    `extend_sat_encodeLinearLe` / `extend_sat_encodeAllDifferent`. -/
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

/-- **Bridge (multi-valued).** A normalized `encodeNotAllEqualMulti` constraint is
    modelled by `extend a bA auxA` (it mentions only thresholds — the encoding is
    aux-free) whenever two of the recovered values differ.  Composes
    `encodeNotAllEqualMulti_sound` with `extend_intValue`; the multi-valued
    (k>2-colour) analogue of `extend_sat_encodeNotAllEqualBin`. -/
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

end CSP.L2S.PB
