import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«02_color»

namespace CSP.L2S.PB.GraphColoring

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for graph 2-colouring (`k3_2col`)

`k3_2col` (`Tests/lean/02_color.lean`) colours the triangle **K₃** with two
colours — the smallest non-2-colourable graph (the odd cycle C₃).  Each vertex
gets a colour variable over `{1,2}`; each of the three edges `(u,v)` is a
`not_equal u v` constraint.  Three mutually-adjacent vertices cannot take only
two colours, so the instance is unsatisfiable.

This is a **new corpus family** (graph colouring, pattern `ne`) on the existing
aux-free not-all-equal machinery: a binary `not_equal u v` edge is exactly
"the two-element set `{u,v}` is not all equal", so it rides on `encodeNotAllEqualBin`
through `csp_unsat_generic` and the bridges `not_equal_sat` /
`extend_sat_encodeNotAllEqualBin` (`NotAllEqualBridge.lean`) — the same shape as
the Schur / van-der-Waerden / Ramsey proofs but with 2-variable edges instead of
3-variable triples.

For the binary colour domain `{1,2}` each variable has a single threshold bit, so
the order-encoding `monotonicity` is empty; vertex `i` maps to OPB `x{i+1}`.  The
six clauses are `x_u + x_v ≥ 1` and `¬x_u + ¬x_v ≥ 1` per edge.
-/

/-! ### The signature, the edge list, and corpus membership -/

/-- The PB signature for `k3_2col`: three integer (colour) variables, each over the
    binary domain `{1,2}`, no Boolean or auxiliary variables. -/
def gcSig : CSPSig where
  nInt := 3
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 2
  sorted := fun _ => domainValues_sorted 1 2
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Every colour variable has the single-threshold (binary) domain, width `1 > 0`. -/
theorem gcSig_width (i : Fin gcSig.nInt) : 0 < gcSig.width i := by
  show 0 < (domainValues 1 2).length - 1; decide

/-- Each edge's `not_equal` constraint is in `k3_2col.constraints` (it is one of the
    `edge_constraints`, the right summand of the list). -/
theorem k3Edges_mem_constraints (e : Fin 3 × Fin 3) (he : e ∈ k3Edges) :
    not_equal e.1 e.2 ∈ k3_2col.constraints := by
  obtain ⟨u, v⟩ := e
  show not_equal u v ∈ bound_constraints 3 2 ++ edge_constraints 3 k3Edges
  apply List.mem_append_right
  rw [edge_constraints, List.mem_map]
  exact ⟨(u, v), he, rfl⟩

/-! ### The PB encoding and certificate -/

/-- The PB user constraints: the normalized not-all-equal encoding of each edge
    (the order-encoding staircase clauses are added by the spine and are empty here). -/
def gcUser : List (PBConstr (PBVar gcSig)) :=
  k3Edges.flatMap (fun e =>
    (encodeNotAllEqualBin [e.1, e.2] (fun i _ => gcSig_width i)).filterMap normalize)

/-- The veripb-elaborated kernel proof of UNSAT for `gcUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The three colour thresholds map to OPB
    `x1,x2,x3`; the six clauses are `x_u + x_v ≥ 1` / `¬x_u + ¬x_v ≥ 1` per edge. -/
def gcKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 6;
rup >= 0 : ~ ;
pol 4 5 + 1 + s;
rup 1 ~x2 >= 1 : ~ 8 2;
rup 1 ~x3 >= 1 : ~ 8 6;
rup 1 ~x2 1 ~x3 >= 2 : 9 10 ~;
pol 3 11 +;
output NONE ;
conclusion UNSAT : 12;
end pseudo-Boolean proof;
"

/-- The PB encoding of `k3_2col` is unsatisfiable — established by the external PB
    certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem gc_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((gcSig.monotonicity ++ gcUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 3 gcKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain 2-colouring under which every edge is
    bichromatic. -/
theorem gc_no_sol : ¬ ∃ (a : Fin gcSig.nInt → Int) (_ : Fin gcSig.nBool → Bool),
    (∀ i, a i ∈ gcSig.values i) ∧ (∀ e ∈ k3Edges, a e.1 ≠ a e.2) := by
  apply csp_unsat_generic gcSig gcUser
    (fun a _ => ∀ e ∈ k3Edges, a e.1 ≠ a e.2)
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    simp only [gcUser, List.mem_flatMap] at hc
    obtain ⟨e, he, hc⟩ := hc
    refine extend_sat_encodeNotAllEqualBin a bA _ hdom [e.1, e.2]
      (fun i _ => gcSig_width i) 1 2
      (fun i _ => by show domainValues 1 2 = [(1 : Int), 2]; decide) ?_ c hc
    exact ⟨e.1, by simp, e.2, by simp, hP e he⟩
  · exact gc_formulaUnsat

/-- **End-to-end graph-2-colouring UNSAT.** The corpus CSP `k3_2col` — colour the
    triangle K₃ with two colours — is unsatisfiable, discharged through the verified
    PB pipeline: the `not_equal` bridge turns any solution into a "differ" fact on
    each edge, the generic spine `csp_unsat_generic` turns those into a PB model, and
    the committed certificate `gc_formulaUnsat` contradicts it. -/
theorem k3_2col_unsat : ¬ k3_2col.isSatisfiable := by
  rintro ⟨a, hsol⟩
  -- Every colour lies in `{1,2}` (from its `bound`).
  have hdom : ∀ i : Fin gcSig.nInt, a i ∈ gcSig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (2 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (2 : ℕ) a hb
    have h2' : a i ≤ 2 := by exact_mod_cast h2
    show a i ∈ domainValues 1 2
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- Every edge is bichromatic (from its `not_equal`).
  have hP : ∀ e ∈ k3Edges, a e.1 ≠ a e.2 := by
    intro e he
    exact not_equal_sat e.1 e.2 a (hsol _ (k3Edges_mem_constraints e he))
  exact gc_no_sol ⟨a, fun _ => false, hdom, hP⟩

end CSP.L2S.PB.GraphColoring
