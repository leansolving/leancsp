import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.NotAllEqual

namespace CSP.L2S.PB

open CSP.L2S

/-!
# PB backend — adapter bridges for the `schur_triple` (not-all-equal) pattern

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
CSPs `vdw_2_3_9` (`VanDerWaerden.lean`) and `ramsey_3_3_K6` (`Ramsey.lean`).
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

end CSP.L2S.PB
