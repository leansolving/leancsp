import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.AllDifferent
import CSP.L2S.Backends.PB.Extend
import CSP.L2S.Tests.lean.«35_pigeonhole»

namespace CSP.L2S.PB.Pigeonhole

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the pigeonhole corpus CSP `php_3_2`

This closes the loop on a *named corpus* problem: `php_3_2`
(`Tests/lean/35_pigeonhole.lean`) — three pigeons into two holes, no two sharing —
is proved `¬ isSatisfiable` through the verified PB pipeline, with no hand-wired
order-encoding soundness.

Pigeonhole's infeasibility comes entirely from `alldifferent` over a domain
smaller than the number of variables (the canonical resolution-hard instance).
The `alldifferent` order encoding is aux-free, so this rides on the existing
`encodeAllDifferent_sound` plus the generic spine `csp_unsat_generic`:

* `alldifferent_sat` — the reusable bridge: a satisfied `alldifferent scope`
  constraint makes the assigned values pairwise distinct (`Nodup`), the analogue of
  `bound_sat` / `linear_le_sat` in `Adapter.lean`;
* `extend_sat_encodeAllDifferent` — the reusable per-constraint soundness fact: a
  normalized `encodeAllDifferent` constraint is modelled by `extend a bA auxA`
  whenever the recovered values are `Nodup` (composes `encodeAllDifferent_sound`
  with `extend_intValue`);
* `php_formulaUnsat` — the committed PB certificate (RoundingSat + veripb,
  kernel-checked through PBLean via `native_decide`);
* `php_3_2_unsat` — the end-to-end theorem, composed through `csp_unsat_generic`.

For `php_3_2` the domain is `{1,2}` (one threshold per pigeon), so `monotonicity`
is empty and the encoding is the two-clause UNSAT core
`Σⱼ ⟦pigeonⱼ = 1⟧ ≤ 1` and `Σⱼ ⟦pigeonⱼ = 2⟧ ≤ 1` over three pigeons.
-/

/-! ### Reusable bridge: `alldifferent` satisfaction ⇒ recovered values `Nodup` -/

/-- A satisfied `alldifferent scope` constraint makes the assigned values along the
    scope pairwise distinct (`Nodup`).  Mirrors `bound_sat` / `linear_le_sat`. -/
theorem alldifferent_sat {n m : ℕ} (scope : _root_.Vector (HomogeneousVarIndex n) m)
    (a : HomogeneousAssignment n)
    (h : HomogeneousCSP.satisfiesConstraint (alldifferent scope) a) :
    (scope.toList.map a).Nodup := by
  simp only [HomogeneousCSP.satisfiesConstraint, alldifferent,
    CSP.satisfies_dynamic_constraint, CSP.satisfies_constraint, CSP.sat,
    decide_eq_true_eq] at h
  rwa [extractValues_map_assignment] at h

/-! ### Reusable `extend`-soundness for normalized `alldifferent` constraints -/

/-- A normalized `encodeAllDifferent` constraint is modelled by `extend a bA auxA`
    (`alldifferent` is aux-free) whenever the recovered values are pairwise distinct.
    Composes `encodeAllDifferent_sound` with `extend_intValue`. -/
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

/-! ### The pigeonhole signature, encoding, and certificate -/

/-- The PB signature for `php_3_2`: three integer variables (pigeons), each over
    the two-element hole domain `{1,2}`, no Boolean or auxiliary variables. -/
def phpSig : CSPSig where
  nInt := 3
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 2
  sorted := fun _ => domainValues_sorted 1 2
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The pigeon variables as the scope of the corpus `alldifferent` (`Vector.ofFn id`). -/
def phpScope : _root_.Vector (HomogeneousVarIndex 3) 3 := _root_.Vector.ofFn id

/-- The pigeon variable list `[0,1,2]` (the `alldifferent` scope as a `List`). -/
def phpVars : List (Fin phpSig.nInt) := phpScope.toList

/-- The PB encoding of `php_3_2`: the (empty) staircase clauses plus the normalized
    `alldifferent` per-value constraints over the shared domain `{1,2}`. -/
def phpEncoded : List (PBConstr (PBVar phpSig)) :=
  phpSig.monotonicity ++ (encodeAllDifferent phpVars [1, 2]).filterMap normalize

/-- The veripb-elaborated kernel proof of UNSAT for `phpEncoded`'s OPB
    serialization (RoundingSat + veripb; both untrusted). -/
def phpKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 2;
rup >= 0 : ~ ;
pol 3 1 1000000000000000 * + 2 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 4;
end pseudo-Boolean proof;
"

/-- The PB encoding of `php_3_2` is unsatisfiable — established by the external PB
    certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). The three threshold variables map to OPB `x1,x2,x3`. -/
theorem php_formulaUnsat :
    VeriPB.Reflect.formulaUnsat (phpEncoded.toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 3 phpKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- **End-to-end pigeonhole UNSAT.** The corpus CSP `php_3_2` (three pigeons into
    two holes, `alldifferent`) is unsatisfiable — discharged through the verified
    PB pipeline: the `alldifferent` bridge turns any solution into pairwise-distinct
    pigeon values, the generic spine `csp_unsat_generic` turns that into a PB model,
    and the committed certificate `php_formulaUnsat` contradicts it. No hand-wired
    order-encoding soundness. -/
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiable := by
  rintro ⟨a, hsol⟩
  -- Every pigeon's value lies in the declared domain `{1,2}` (from its `bound`).
  have hdom : ∀ i : Fin phpSig.nInt, a i ∈ phpSig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (2 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (2 : ℕ) a hb
    have h2' : a i ≤ 2 := by exact_mod_cast h2
    show a i ∈ domainValues 1 2
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- The pigeon values are pairwise distinct (from the `alldifferent`).
  have hnodup : (phpVars.map a).Nodup := by
    have ha : HomogeneousCSP.satisfiesConstraint (php_alldiff 3) a :=
      hsol _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    exact alldifferent_sat phpScope a ha
  -- The generic spine rules out any in-domain, pairwise-distinct solution.
  have key : ¬ ∃ (a : Fin phpSig.nInt → Int) (_ : Fin phpSig.nBool → Bool),
      (∀ i, a i ∈ phpSig.values i) ∧ (phpVars.map a).Nodup := by
    apply csp_unsat_generic phpSig
      ((encodeAllDifferent phpVars [1, 2]).filterMap normalize)
      (fun a _ => (phpVars.map a).Nodup)
      (fun _ _ _ => false)
    · intro a' bA hdom' hnodup' c hc
      exact extend_sat_encodeAllDifferent a' bA _ hdom' phpVars [1, 2] c hc hnodup'
    · exact php_formulaUnsat
  exact key ⟨a, fun _ => false, hdom, hnodup⟩

end CSP.L2S.PB.Pigeonhole
