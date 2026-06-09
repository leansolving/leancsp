import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«34_ramsey»

namespace CSP.L2S.PB.Ramsey

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the Ramsey corpus CSP `ramsey_3_3_K6`

`ramsey_3_3_K6` (`Tests/lean/34_ramsey.lean`) is the CSP form of the Ramsey bound
**R(3,3) = 6**: every 2-colouring of the edges of `K₆` contains a monochromatic
triangle.  `K₆` has 15 edges (the variables, binary colour domain `{0,1}`); each
of the 20 triangles becomes a `schur_triple` (not-all-equal) constraint over its
three edge variables.

Like `vdw_2_3_9`, this rides on the aux-free not-all-equal encoder through the
generic spine `csp_unsat_generic` and the reusable bridges `schur_triple_sat` /
`extend_sat_encodeNotAllEqualBin` (`NotAllEqualBridge.lean`):

* `ramseyT_mem_constraints` is the corpus-membership step (each generated triangle's
  `schur_triple` constraint really is in `ramsey_3_3_K6.constraints`);
* `ramsey_formulaUnsat` is the committed PB certificate (RoundingSat + veripb,
  kernel-checked through PBLean by `native_decide`);
* `ramsey_3_3_K6_unsat` is the end-to-end theorem.

For the binary domain `{0,1}` each variable has a single threshold bit, so the
order-encoding `monotonicity` is empty and the encoding is the two clauses
`Σ ⟦edgeⱼ = 0⟧ ≥ 1`, `Σ ⟦edgeⱼ = 1⟧ ≥ 1` per triangle.  Edge `e` maps to OPB
`x{e+1}`.
-/

/-! ### The signature, the resolved triangle list, and corpus membership -/

/-- The PB signature for `ramsey_3_3_K6`: one integer (colour) variable per edge of
    `K₆` (15 of them), each over the binary domain `{0,1}`. -/
def ramseySig : CSPSig where
  nInt := ramsey_num_edges 6
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Every edge variable has the single-threshold (binary) domain, width `1 > 0`. -/
theorem ramseySig_width (i : Fin ramseySig.nInt) : 0 < ramseySig.width i := by
  show 0 < (domainValues 0 1).length - 1; decide

/-- The corpus triangles resolved to in-range edge-variable indices (every triangle
    in `ramsey_triangles 6` has in-range edge indices, so the guards always fire). -/
def ramseyT :
    List (Fin (ramsey_num_edges 6) × Fin (ramsey_num_edges 6) × Fin (ramsey_num_edges 6)) :=
  (ramsey_triangles 6).filterMap (fun p =>
    if h1 : p.1 < ramsey_num_edges 6 then if h2 : p.2.1 < ramsey_num_edges 6 then
      if h3 : p.2.2 < ramsey_num_edges 6 then
        some (⟨p.1, h1⟩, ⟨p.2.1, h2⟩, ⟨p.2.2, h3⟩) else none else none else none)

/-- Each resolved triangle's `schur_triple` constraint is in `ramsey_3_3_K6.constraints`
    (it is one of the `ramsey_constraints`, the right summand of the constraint list). -/
theorem ramseyT_mem_constraints
    (t : Fin (ramsey_num_edges 6) × Fin (ramsey_num_edges 6) × Fin (ramsey_num_edges 6))
    (ht : t ∈ ramseyT) :
    schur_triple t.1 t.2.1 t.2.2 ∈ ramsey_3_3_K6.constraints := by
  rw [ramseyT, List.mem_filterMap] at ht
  obtain ⟨p, hp_mem, hp_eq⟩ := ht
  obtain ⟨i, j, k⟩ := p
  simp only at hp_eq
  split_ifs at hp_eq with h1 h2 h3
  rw [Option.some.injEq] at hp_eq
  subst hp_eq
  show schur_triple (⟨i, h1⟩ : Fin (ramsey_num_edges 6)) ⟨j, h2⟩ ⟨k, h3⟩ ∈
    ramsey_bounds 6 ++ ramsey_constraints 6
  apply List.mem_append_right
  unfold ramsey_constraints
  rw [List.mem_filterMap]
  exact ⟨(i, j, k), hp_mem, by simp only [dif_pos h1, dif_pos h2, dif_pos h3]⟩

/-! ### The PB encoding and certificate -/

/-- The PB user constraints: the normalized not-all-equal encoding of each triangle
    (the order-encoding staircase clauses are added by the spine and are empty here). -/
def ramseyUser : List (PBConstr (PBVar ramseySig)) :=
  ramseyT.flatMap (fun t =>
    (encodeNotAllEqualBin [t.1, t.2.1, t.2.2] (fun i _ => ramseySig_width i)).filterMap normalize)

/-- The veripb-elaborated kernel proof of UNSAT for `ramseyUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The 15 edge thresholds map to OPB
    `x1,…,x15`. -/
def ramseyKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 40;
rup >= 0 : ~ ;
pol 22 9 + 3 + s;
pol 24 11 + 5 + s;
pol 26 13 + 7 + s;
pol 39 20 + 18 + s 44 + 16 + s 43 + s 42 + s 1 + s;
pol 37 20 + 12 + s;
pol 35 18 + 10 + s;
pol 28 15 + 3 + s 47 + 5 + s 46 + s 14 + s;
pol 30 17 + 3 + s;
pol 32 19 + 5 + s;
pol 33 16 + 12 + s 50 + 10 + s 49 + s 7 + s 48 + s 45 + s;
pol 27 16 + 4 + 51 + s;
pol 23 12 + 2 + 51 + s;
pol 36 13 + 9 + s 53 + 17 + s 52 + s 6 + 51 + s;
pol 40 15 + 17 + s;
pol 38 13 + 11 + s;
pol 21 10 + 2 + 51 + s 56 + 4 + 51 + s 55 + s 19 + s 54 + s;
rup 1 ~x9 >= 1 : ~ 57 51 8;
pol 29 58 + 18 + 57 + 4 + 51 + s;
pol 25 58 + 14 + 57 + 2 + 51 + s;
rup 1 x10 >= 1 : ~ 60 59 9;
pol 34 61 + 11 + 60 + 15 + 59 + s;
rup 1 ~x8 >= 1 : ~ 62 51 6;
rup 1 ~x15 >= 1 : ~ 62 57 20;
rup 1 ~x8 1 ~x9 1 ~x15 >= 3 : 64 63 58 ~;
pol 31 65 +;
output NONE ;
conclusion UNSAT : 66;
end pseudo-Boolean proof;
"

/-- The PB encoding of `ramsey_3_3_K6` is unsatisfiable — established by the external
    PB certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem ramsey_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((ramseySig.monotonicity ++ ramseyUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ (ramsey_num_edges 6) ramseyKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain edge-colouring under which every
    triangle is not monochromatic. -/
theorem ramsey_no_sol : ¬ ∃ (a : Fin ramseySig.nInt → Int) (_ : Fin ramseySig.nBool → Bool),
    (∀ i, a i ∈ ramseySig.values i) ∧
    (∀ t ∈ ramseyT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2) := by
  apply csp_unsat_generic ramseySig ramseyUser
    (fun a _ => ∀ t ∈ ramseyT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2)
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    simp only [ramseyUser, List.mem_flatMap] at hc
    obtain ⟨t, ht, hc⟩ := hc
    refine extend_sat_encodeNotAllEqualBin a bA _ hdom [t.1, t.2.1, t.2.2]
      (fun i _ => ramseySig_width i) 0 1
      (fun i _ => by show domainValues 0 1 = [(0 : Int), 1]; decide) ?_ c hc
    rcases hP t ht with h | h | h
    · exact ⟨t.1, by simp, t.2.1, by simp, h⟩
    · exact ⟨t.1, by simp, t.2.2, by simp, h⟩
    · exact ⟨t.2.1, by simp, t.2.2, by simp, h⟩
  · exact ramsey_formulaUnsat

/-- **End-to-end Ramsey UNSAT.** The corpus CSP `ramsey_3_3_K6` — the R(3,3) = 6
    instance, "every 2-colouring of the edges of `K₆` has a monochromatic triangle" —
    is unsatisfiable, discharged through the verified PB pipeline: the `schur_triple`
    bridge turns any solution into not-all-equal facts on each triangle, the generic
    spine `csp_unsat_generic` turns those into a PB model, and the committed
    certificate `ramsey_formulaUnsat` contradicts it.  No hand-wired order-encoding
    soundness. -/
theorem ramsey_3_3_K6_unsat : ¬ ramsey_3_3_K6.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Every edge colour lies in `{0,1}` (from its `bound`).
  have hdom : ∀ i : Fin ramseySig.nInt, a i ∈ ramseySig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 0 1) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 0 1 a hb
    show a i ∈ domainValues 0 1
    exact mem_domainValues.mpr ⟨h1, h2⟩
  -- Every triangle is not monochromatic (from its `schur_triple`).
  have hP : ∀ t ∈ ramseyT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2 := by
    intro t ht
    exact schur_triple_sat t.1 t.2.1 t.2.2 a (hsol _ (ramseyT_mem_constraints t ht))
  exact ramsey_no_sol ⟨a, fun _ => false, hdom, hP⟩

end CSP.L2S.PB.Ramsey
