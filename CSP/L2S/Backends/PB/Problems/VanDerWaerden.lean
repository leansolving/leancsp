import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«33_van_der_waerden»

namespace CSP.L2S.PB.VanDerWaerden

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the van der Waerden corpus CSP `vdw_2_3_9`

`vdw_2_3_9` (`Tests/lean/33_van_der_waerden.lean`) is the CSP form of the van der
Waerden bound **W(2,3) = 9**: every 2-colouring of `{1,…,9}` contains a
monochromatic 3-term arithmetic progression.  Each of the 16 APs becomes a
`schur_triple` (not-all-equal) constraint over its three colour variables; the
binary colour domain is `{0,1}`.

This rides on the aux-free not-all-equal encoder through the generic spine
`csp_unsat_generic`, exactly as pigeonhole rode on `alldifferent`:

* the reusable bridges `schur_triple_sat` / `extend_sat_encodeNotAllEqualBin`
  (`NotAllEqualBridge.lean`) turn a solution into "the three values are not all
  equal" facts and turn those into a PB model;
* `vdwT_mem_constraints` is the corpus-membership step (each generated AP triple's
  `schur_triple` constraint really is in `vdw_2_3_9.constraints`);
* `vdw_formulaUnsat` is the committed PB certificate (RoundingSat + veripb,
  kernel-checked through PBLean by `native_decide`);
* `vdw_2_3_9_unsat` is the end-to-end theorem, composed through `csp_unsat_generic`.

For the binary domain `{0,1}` each variable has a single threshold bit, so the
order-encoding `monotonicity` is empty and the PB encoding is just the two clauses
`Σ ⟦colourⱼ = 0⟧ ≥ 1`, `Σ ⟦colourⱼ = 1⟧ ≥ 1` per AP — the textbook van der Waerden
SAT encoding.  Variable `i` (integer `i+1`) maps to OPB `x{i+1}`.
-/

/-! ### The signature, the resolved AP-triple list, and corpus membership -/

/-- The PB signature for `vdw_2_3_9`: nine integer (colour) variables, each over the
    binary domain `{0,1}`, no Boolean or auxiliary variables. -/
def vdwSig : CSPSig where
  nInt := 9
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Every colour variable has the single-threshold (binary) domain, width `1 > 0`. -/
theorem vdwSig_width (i : Fin vdwSig.nInt) : 0 < vdwSig.width i := by
  show 0 < (domainValues 0 1).length - 1; decide

/-- The corpus AP triples resolved to in-range `Fin 9` variable indices (every AP in
    `vdw_ap_triples 9` is within range, so the guards always fire). -/
def vdwT : List (Fin 9 × Fin 9 × Fin 9) :=
  (vdw_ap_triples 9).filterMap (fun p =>
    if h1 : p.1 < 9 then if h2 : p.2.1 < 9 then if h3 : p.2.2 < 9 then
      some (⟨p.1, h1⟩, ⟨p.2.1, h2⟩, ⟨p.2.2, h3⟩) else none else none else none)

/-- Each resolved AP triple's `schur_triple` constraint is in `vdw_2_3_9.constraints`
    (it is one of the `vdw_constraints`, the right summand of the constraint list). -/
theorem vdwT_mem_constraints (t : Fin 9 × Fin 9 × Fin 9) (ht : t ∈ vdwT) :
    schur_triple t.1 t.2.1 t.2.2 ∈ vdw_2_3_9.constraints := by
  rw [vdwT, List.mem_filterMap] at ht
  obtain ⟨p, hp_mem, hp_eq⟩ := ht
  obtain ⟨i, j, k⟩ := p
  simp only at hp_eq
  split_ifs at hp_eq with h1 h2 h3
  rw [Option.some.injEq] at hp_eq
  subst hp_eq
  show schur_triple (⟨i, h1⟩ : Fin 9) ⟨j, h2⟩ ⟨k, h3⟩ ∈
    vdw_bounds 9 ++ vdw_constraints 9 (vdw_ap_triples 9)
  apply List.mem_append_right
  rw [vdw_constraints, List.mem_filterMap]
  exact ⟨(i, j, k), hp_mem, by simp only [dif_pos h1, dif_pos h2, dif_pos h3]⟩

/-! ### The PB encoding and certificate -/

/-- The PB user constraints: the normalized not-all-equal encoding of each AP triple
    (the order-encoding staircase clauses are added by the spine and are empty here). -/
def vdwUser : List (PBConstr (PBVar vdwSig)) :=
  vdwT.flatMap (fun t =>
    (encodeNotAllEqualBin [t.1, t.2.1, t.2.2] (fun i _ => vdwSig_width i)).filterMap normalize)

/-- The veripb-elaborated kernel proof of UNSAT for `vdwUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The nine colour thresholds map to OPB
    `x1,…,x9`. -/
def vdwKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 32;
rup >= 0 : ~ ;
pol 7 20 + 18 + s 11 + 5 + s;
pol 25 32 + 20 + s 13 + s 7 + s 16 + s 34 + s 1 + s;
pol 14 29 + 25 + s 12 + s 5 + s;
pol 19 28 + 26 + s 18 + s;
pol 21 10 + 20 + s 3 + s 7 + s 37 + 36 + s 35 + s;
pol 6 38 + 21 + 25 + s;
pol 19 4 + 38 + 8 + 38 + s 39 + s;
pol 14 9 + 31 + 22 + 40 + s 26 + 40 + s 4 + 38 + s 8 + 38 + s;
pol 2 38 + 13 + 41 + 15 + 41 + 30 + 40 + 6 + 38 + s;
rup 1 x9 >= 1 : ~ 42 41 27;
rup 1 x3 >= 1 : ~ 42 41 17;
rup 1 x3 1 x9 1 x6 >= 3 : 43 44 40 ~;
pol 20 45 +;
output NONE ;
conclusion UNSAT : 46;
end pseudo-Boolean proof;
"

/-- The PB encoding of `vdw_2_3_9` is unsatisfiable — established by the external PB
    certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem vdw_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((vdwSig.monotonicity ++ vdwUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 9 vdwKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain colouring under which every AP triple
    is not monochromatic. -/
theorem vdw_no_sol : ¬ ∃ (a : Fin vdwSig.nInt → Int) (_ : Fin vdwSig.nBool → Bool),
    (∀ i, a i ∈ vdwSig.values i) ∧
    (∀ t ∈ vdwT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2) := by
  apply csp_unsat_generic vdwSig vdwUser
    (fun a _ => ∀ t ∈ vdwT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2)
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    simp only [vdwUser, List.mem_flatMap] at hc
    obtain ⟨t, ht, hc⟩ := hc
    refine extend_sat_encodeNotAllEqualBin a bA _ hdom [t.1, t.2.1, t.2.2]
      (fun i _ => vdwSig_width i) 0 1
      (fun i _ => by show domainValues 0 1 = [(0 : Int), 1]; decide) ?_ c hc
    rcases hP t ht with h | h | h
    · exact ⟨t.1, by simp, t.2.1, by simp, h⟩
    · exact ⟨t.1, by simp, t.2.2, by simp, h⟩
    · exact ⟨t.2.1, by simp, t.2.2, by simp, h⟩
  · exact vdw_formulaUnsat

/-- **End-to-end van der Waerden UNSAT.** The corpus CSP `vdw_2_3_9` — the W(2,3) = 9
    instance, "every 2-colouring of `{1,…,9}` has a monochromatic 3-term AP" — is
    unsatisfiable, discharged through the verified PB pipeline: the `schur_triple`
    bridge turns any solution into not-all-equal facts on each AP, the generic spine
    `csp_unsat_generic` turns those into a PB model, and the committed certificate
    `vdw_formulaUnsat` contradicts it.  No hand-wired order-encoding soundness. -/
theorem vdw_2_3_9_unsat : ¬ vdw_2_3_9.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Every colour lies in `{0,1}` (from its `bound`).
  have hdom : ∀ i : Fin vdwSig.nInt, a i ∈ vdwSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 0 1) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 0 1 a hb
    show a i ∈ domainValues 0 1
    exact mem_domainValues.mpr ⟨h1, h2⟩
  -- Every AP triple is not monochromatic (from its `schur_triple`).
  have hP : ∀ t ∈ vdwT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2 := by
    intro t ht
    exact schur_triple_sat t.1 t.2.1 t.2.2 a (hsol _ (vdwT_mem_constraints t ht))
  exact vdw_no_sol ⟨a, fun _ => false, hdom, hP⟩

end CSP.L2S.PB.VanDerWaerden
