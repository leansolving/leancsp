import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«02_color»

namespace CSP.L2S.PB.ForbiddenColoring

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for forbidden-colour `k2_forbidden`

`k2_forbidden` (`Tests/lean/02_color.lean`) colours the single edge **K₂**
(vertices 0–1) with two colours `{1,2}`, but **forbids colour 1 at both
endpoints** (`not_equals_const v 1` per vertex).  Forbidding colour 1 forces both
vertices to colour 2, which contradicts the edge `not_equal 0 1` — so the
instance is unsatisfiable.

This is the **first end-to-end consumer of `encodeNeConst`** (the verified
`xⱼ ≠ const` encoder, `AllDifferent.lean`), exercised alongside `not_equal`.  Both
are aux-free, so the instance rides on the generic spine `csp_unsat_generic`
through four bridges: `not_equal_sat` / `extend_sat_encodeNotAllEqualBin` for the
edge, and the new `not_equals_const_sat` / `extend_sat_encodeNeConst` for the
forbidden colours (`NotAllEqualBridge.lean`).

For the binary colour domain `{1,2}` each variable has a single threshold bit, so
the order-encoding `monotonicity` is empty; vertex `i` maps to OPB `x{i+1}`.  The
four clauses are the edge's `x1 + x2 ≥ 1` / `¬x1 + ¬x2 ≥ 1` and the two forbidden
`¬x1 ≥ 1` / `¬x2 ≥ 1`.
-/

/-! ### The signature, corpus membership -/

/-- The PB signature for `k2_forbidden`: two integer (colour) variables, each over
    the binary domain `{1,2}`, no Boolean or auxiliary variables. -/
def fcSig : CSPSig where
  nInt := 2
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 2
  sorted := fun _ => domainValues_sorted 1 2
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Every colour variable has the single-threshold (binary) domain, width `1 > 0`. -/
theorem fcSig_width (i : Fin fcSig.nInt) : 0 < fcSig.width i := by
  show 0 < (domainValues 1 2).length - 1; decide

/-- Each edge's `not_equal` constraint is in `k2_forbidden.constraints`. -/
theorem k2Edges_mem_constraints (e : Fin 2 × Fin 2) (he : e ∈ k2Edges) :
    not_equal e.1 e.2 ∈ k2_forbidden.constraints := by
  obtain ⟨u, v⟩ := e
  show not_equal u v ∈ (bound_constraints 2 2 ++ edge_constraints 2 k2Edges)
        ++ k2Forbidden.map (fun p => not_equals_const p.1 p.2)
  apply List.mem_append_left
  apply List.mem_append_right
  rw [edge_constraints, List.mem_map]
  exact ⟨(u, v), he, rfl⟩

/-- Each forbidden colour's `not_equals_const` constraint is in `k2_forbidden.constraints`. -/
theorem k2Forbidden_mem_constraints (p : Fin 2 × ℤ) (hp : p ∈ k2Forbidden) :
    not_equals_const p.1 p.2 ∈ k2_forbidden.constraints := by
  obtain ⟨u, c⟩ := p
  show not_equals_const u c ∈ (bound_constraints 2 2 ++ edge_constraints 2 k2Edges)
        ++ k2Forbidden.map (fun p => not_equals_const p.1 p.2)
  apply List.mem_append_right
  rw [List.mem_map]
  exact ⟨(u, c), hp, rfl⟩

/-! ### The PB encoding and certificate -/

/-- The PB user constraints: the not-all-equal encoding of the edge, appended with
    the `encodeNeConst` encoding of each forbidden colour (the order-encoding
    staircase clauses are added by the spine and are empty here). -/
def fcUser : List (PBConstr (PBVar fcSig)) :=
  (k2Edges.flatMap (fun e =>
    (encodeNotAllEqualBin [e.1, e.2] (fun i _ => fcSig_width i)).filterMap normalize))
  ++ (k2Forbidden.flatMap (fun p => (normalize (encodeNeConst p.1 p.2)).toList))

/-- The veripb-elaborated kernel proof of UNSAT for `fcUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The two colour thresholds map to OPB
    `x1,x2`; the four clauses are the edge `x1+x2 ≥ 1` / `¬x1+¬x2 ≥ 1` and the
    forbidden `¬x1 ≥ 1` / `¬x2 ≥ 1`. -/
def fcKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 4;
rup >= 0 : ~ ;
rup 1 x2 >= 1 : ~ 3 1;
pol 4 6 +;
output NONE ;
conclusion UNSAT : 7;
end pseudo-Boolean proof;
"

/-- The PB encoding of `k2_forbidden` is unsatisfiable — established by the external
    PB certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem fc_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((fcSig.monotonicity ++ fcUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 2 fcKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain 2-colouring under which the edge is
    bichromatic and every forbidden colour is respected. -/
theorem fc_no_sol : ¬ ∃ (a : Fin fcSig.nInt → Int) (_ : Fin fcSig.nBool → Bool),
    (∀ i, a i ∈ fcSig.values i) ∧
    ((∀ e ∈ k2Edges, a e.1 ≠ a e.2) ∧ (∀ p ∈ k2Forbidden, a p.1 ≠ p.2)) := by
  apply csp_unsat_generic fcSig fcUser
    (fun a _ => (∀ e ∈ k2Edges, a e.1 ≠ a e.2) ∧ (∀ p ∈ k2Forbidden, a p.1 ≠ p.2))
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    simp only [fcUser, List.mem_append] at hc
    rcases hc with hc | hc
    · -- edge clause
      simp only [List.mem_flatMap] at hc
      obtain ⟨e, he, hc⟩ := hc
      refine extend_sat_encodeNotAllEqualBin a bA _ hdom [e.1, e.2]
        (fun i _ => fcSig_width i) 1 2
        (fun i _ => by show domainValues 1 2 = [(1 : Int), 2]; decide) ?_ c hc
      exact ⟨e.1, by simp, e.2, by simp, hP.1 e he⟩
    · -- forbidden clause
      simp only [List.mem_flatMap] at hc
      obtain ⟨p, hp, hc⟩ := hc
      rw [Option.mem_toList] at hc
      exact extend_sat_encodeNeConst a bA _ hdom p.1 p.2 (hP.2 p hp) c hc
  · exact fc_formulaUnsat

/-- **End-to-end forbidden-colour UNSAT.** The corpus CSP `k2_forbidden` — colour the
    edge K₂ with two colours while forbidding colour 1 at both endpoints — is
    unsatisfiable, discharged through the verified PB pipeline: the `not_equal` /
    `not_equals_const` bridges turn any solution into "differ" facts on the edge and
    the forbidden colours, the generic spine `csp_unsat_generic` turns those into a PB
    model, and the committed certificate `fc_formulaUnsat` contradicts it. -/
theorem k2_forbidden_unsat : ¬ k2_forbidden.isSatisfiable := by
  rintro ⟨a, hsol⟩
  -- Every colour lies in `{1,2}` (from its `bound`).
  have hdom : ∀ i : Fin fcSig.nInt, a i ∈ fcSig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (2 : ℕ)) a := by
      apply hsol
      apply List.mem_append_left
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 1 (2 : ℕ) a hb
    have h2' : a i ≤ 2 := by exact_mod_cast h2
    show a i ∈ domainValues 1 2
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- The edge is bichromatic (from its `not_equal`).
  have hEdge : ∀ e ∈ k2Edges, a e.1 ≠ a e.2 := by
    intro e he
    exact not_equal_sat e.1 e.2 a (hsol _ (k2Edges_mem_constraints e he))
  -- Each forbidden colour is respected (from its `not_equals_const`).
  have hForb : ∀ p ∈ k2Forbidden, a p.1 ≠ p.2 := by
    intro p hp
    exact not_equals_const_sat p.1 p.2 a (hsol _ (k2Forbidden_mem_constraints p hp))
  exact fc_no_sol ⟨a, fun _ => false, hdom, hEdge, hForb⟩

end CSP.L2S.PB.ForbiddenColoring
