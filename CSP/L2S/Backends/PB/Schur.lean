import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«11_schur»

namespace CSP.L2S.PB.Schur

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the Schur corpus CSP `schur_2_5`

`schur_2_5` (`Tests/lean/11_schur.lean`) is the CSP form of the Schur bound
**S(2) = 4**: `{1,…,5}` cannot be partitioned into two sum-free sets.  Each ball
`1..5` gets a colour variable over `{1,2}`; for every sum triple `x + y = z`
(`x ≤ y`, `z ≤ 5`) the three colours are **not all equal** — a `schur_triple`
constraint.  Crucially this includes the *diagonal* triples `1+1=2` and `2+2=4`
(`generate_schur_triples` was fixed to emit `j ≥ i`); without them `{1,…,5}` would
be 2-colourable and the instance would be satisfiable.

Like `vdw_2_3_9` / `ramsey_3_3_K6` this rides on the aux-free not-all-equal encoder
through `csp_unsat_generic` and the reusable bridges `schur_triple_sat` /
`extend_sat_encodeNotAllEqualBin` (`NotAllEqualBridge.lean`).  A diagonal triple
`(i,i,k)` encodes a repeated threshold literal (`xᵢ + xᵢ + xₖ ≥ 1`), which the PB
pipeline handles directly.

For the binary colour domain `{1,2}` each variable has a single threshold bit, so
the order-encoding `monotonicity` is empty.  Ball `i+1` maps to OPB `x{i+1}`.
-/

/-! ### The signature, the resolved triple list, and corpus membership -/

/-- The PB signature for `schur_2_5`: five integer (colour) variables, each over the
    binary domain `{1,2}`, no Boolean or auxiliary variables. -/
def schurSig : CSPSig where
  nInt := 5
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 2
  sorted := fun _ => domainValues_sorted 1 2
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Every colour variable has the single-threshold (binary) domain, width `1 > 0`. -/
theorem schurSig_width (i : Fin schurSig.nInt) : 0 < schurSig.width i := by
  show 0 < (domainValues 1 2).length - 1; decide

/-- The corpus sum triples resolved to in-range `Fin 5` variable indices. -/
def schurT : List (Fin 5 × Fin 5 × Fin 5) :=
  (generate_schur_triples 5).filterMap (fun p =>
    if h1 : p.1 < 5 then if h2 : p.2.1 < 5 then if h3 : p.2.2 < 5 then
      some (⟨p.1, h1⟩, ⟨p.2.1, h2⟩, ⟨p.2.2, h3⟩) else none else none else none)

/-- Each resolved sum triple's `schur_triple` constraint is in `schur_2_5.constraints`
    (it is one of the `make_schur_constraints`, the right summand of the list). -/
theorem schurT_mem_constraints (t : Fin 5 × Fin 5 × Fin 5) (ht : t ∈ schurT) :
    schur_triple t.1 t.2.1 t.2.2 ∈ schur_2_5.constraints := by
  rw [schurT, List.mem_filterMap] at ht
  obtain ⟨p, hp_mem, hp_eq⟩ := ht
  obtain ⟨i, j, k⟩ := p
  simp only at hp_eq
  split_ifs at hp_eq with h1 h2 h3
  rw [Option.some.injEq] at hp_eq
  subst hp_eq
  show schur_triple (⟨i, h1⟩ : Fin 5) ⟨j, h2⟩ ⟨k, h3⟩ ∈
    schur_bounds 5 2 ++ make_schur_constraints 5 (generate_schur_triples 5)
  apply List.mem_append_right
  rw [make_schur_constraints, List.mem_filterMap]
  exact ⟨(i, j, k), hp_mem, by simp only [dif_pos h1, dif_pos h2, dif_pos h3]⟩

/-! ### The PB encoding and certificate -/

/-- The PB user constraints: the normalized not-all-equal encoding of each sum triple
    (the order-encoding staircase clauses are added by the spine and are empty here). -/
def schurUser : List (PBConstr (PBVar schurSig)) :=
  schurT.flatMap (fun t =>
    (encodeNotAllEqualBin [t.1, t.2.1, t.2.2] (fun i _ => schurSig_width i)).filterMap normalize)

/-- The veripb-elaborated kernel proof of UNSAT for `schurUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The five colour thresholds map to OPB
    `x1,…,x5`; the diagonal triples `1+1=2` / `2+2=4` give the repeated-literal
    clauses `x1+x1+x2 ≥ 1` / `x2+x2+x4 ≥ 1`. -/
def schurKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 12;
rup >= 0 : ~ ;
pol 1 s;
pol 2 s;
pol 9 s;
pol 10 s;
pol 12 5 + 7 + s 17 + s 14 + s;
rup 1 ~x2 >= 1 : ~ 18 15;
rup 1 x4 >= 1 : ~ 19 16;
rup 1 ~x5 >= 1 : ~ 20 18 8;
rup 1 ~x3 >= 1 : ~ 20 18 6;
rup 1 ~x2 1 ~x3 1 ~x5 >= 3 : 21 22 19 ~;
pol 11 23 +;
output NONE ;
conclusion UNSAT : 24;
end pseudo-Boolean proof;
"

/-- The PB encoding of `schur_2_5` is unsatisfiable — established by the external PB
    certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem schur_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((schurSig.monotonicity ++ schurUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 5 schurKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain colouring under which every sum triple
    is not monochromatic. -/
theorem schur_no_sol : ¬ ∃ (a : Fin schurSig.nInt → Int) (_ : Fin schurSig.nBool → Bool),
    (∀ i, a i ∈ schurSig.values i) ∧
    (∀ t ∈ schurT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2) := by
  apply csp_unsat_generic schurSig schurUser
    (fun a _ => ∀ t ∈ schurT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2)
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    simp only [schurUser, List.mem_flatMap] at hc
    obtain ⟨t, ht, hc⟩ := hc
    refine extend_sat_encodeNotAllEqualBin a bA _ hdom [t.1, t.2.1, t.2.2]
      (fun i _ => schurSig_width i) 1 2
      (fun i _ => by show domainValues 1 2 = [(1 : Int), 2]; decide) ?_ c hc
    rcases hP t ht with h | h | h
    · exact ⟨t.1, by simp, t.2.1, by simp, h⟩
    · exact ⟨t.1, by simp, t.2.2, by simp, h⟩
    · exact ⟨t.2.1, by simp, t.2.2, by simp, h⟩
  · exact schur_formulaUnsat

/-- **End-to-end Schur UNSAT.** The corpus CSP `schur_2_5` — the S(2) = 4 instance,
    "`{1,…,5}` cannot be 2-coloured sum-free" — is unsatisfiable, discharged through
    the verified PB pipeline: the `schur_triple` bridge turns any solution into
    not-all-equal facts on each sum triple (including the diagonals `1+1=2`, `2+2=4`),
    the generic spine `csp_unsat_generic` turns those into a PB model, and the
    committed certificate `schur_formulaUnsat` contradicts it. -/
theorem schur_2_5_unsat : ¬ schur_2_5.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Every colour lies in `{1,2}` (from its `bound`).
  have hdom : ∀ i : Fin schurSig.nInt, a i ∈ schurSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 1 (2 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (2 : ℕ) a hb
    have h2' : a i ≤ 2 := by exact_mod_cast h2
    show a i ∈ domainValues 1 2
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- Every sum triple is not monochromatic (from its `schur_triple`).
  have hP : ∀ t ∈ schurT, a t.1 ≠ a t.2.1 ∨ a t.1 ≠ a t.2.2 ∨ a t.2.1 ≠ a t.2.2 := by
    intro t ht
    exact schur_triple_sat t.1 t.2.1 t.2.2 a (hsol _ (schurT_mem_constraints t ht))
  exact schur_no_sol ⟨a, fun _ => false, hdom, hP⟩

end CSP.L2S.PB.Schur
