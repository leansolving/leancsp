import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.AllDifferent
import CSP.L2S.Backends.PB.Extend
import CSP.L2S.Backends.PB.NotAllEqualBridge
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

/-! ### The pigeonhole signature, encoding, and certificate

The reusable bridges `alldifferent_sat` / `extend_sat_encodeAllDifferent` now live
in `NotAllEqualBridge.lean` (shared, test-file-free) so they can also serve the
graph-colouring proofs. -/

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

/-! ### A larger instance: `php_5_4` (five pigeons, four holes)

Same `alldifferent` recipe as `php_3_2`, scaled up: five pigeons over the
four-hole domain `{1,2,3,4}` (width 3, so `monotonicity` is non-empty). Reuses the
`alldifferent_sat` / `extend_sat_encodeAllDifferent` bridges verbatim. -/

/-- The PB signature for `php_5_4`: five integer variables over `{1,2,3,4}`. -/
def php5Sig : CSPSig where
  nInt := 5
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 4
  sorted := fun _ => domainValues_sorted 1 4
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The pigeon variables as the scope of the corpus `alldifferent`. -/
def php5Scope : _root_.Vector (HomogeneousVarIndex 5) 5 := _root_.Vector.ofFn id

/-- The pigeon variable list (the `alldifferent` scope as a `List`). -/
def php5Vars : List (Fin php5Sig.nInt) := php5Scope.toList

/-- The PB encoding of `php_5_4`: staircase clauses plus the normalized
    `alldifferent` per-value constraints over the shared domain `{1,2,3,4}`. -/
def php5Encoded : List (PBConstr (PBVar php5Sig)) :=
  php5Sig.monotonicity ++ (encodeAllDifferent php5Vars [1, 2, 3, 4]).filterMap normalize

/-- The veripb-elaborated kernel proof of UNSAT for `php5Encoded`'s OPB
    serialization (RoundingSat + veripb; both untrusted). The 15 thresholds map to
    OPB `x1,…,x15`. -/
def php5KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 14;
rup >= 0 : ~ ;
pol 15 11 1000000000000000 * + 12 1000000000000000 * + 13 1000000000000000 * + 14 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 16;
end pseudo-Boolean proof;
"

/-- The PB encoding of `php_5_4` is unsatisfiable — kernel-checked through PBLean's
    verified reflection checker (`native_decide`; RoundingSat / veripb / serializer
    untrusted). -/
theorem php5_formulaUnsat :
    VeriPB.Reflect.formulaUnsat (php5Encoded.toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 15 php5KernelProof (by native_decide)

/-- **End-to-end pigeonhole UNSAT (larger instance).** The corpus CSP `php_5_4`
    (five pigeons into four holes, `alldifferent`) is unsatisfiable, via the same
    verified PB pipeline as `php_3_2` — only the instance size and certificate
    differ. -/
theorem php_5_4_unsat : ¬ php_5_4.isSatisfiable := by
  rintro ⟨a, hsol⟩
  have hdom : ∀ i : Fin php5Sig.nInt, a i ∈ php5Sig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (4 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (4 : ℕ) a hb
    have h2' : a i ≤ 4 := by exact_mod_cast h2
    show a i ∈ domainValues 1 4
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  have hnodup : (php5Vars.map a).Nodup := by
    have ha : HomogeneousCSP.satisfiesConstraint (php_alldiff 5) a :=
      hsol _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    exact alldifferent_sat php5Scope a ha
  have key : ¬ ∃ (a : Fin php5Sig.nInt → Int) (_ : Fin php5Sig.nBool → Bool),
      (∀ i, a i ∈ php5Sig.values i) ∧ (php5Vars.map a).Nodup := by
    apply csp_unsat_generic php5Sig
      ((encodeAllDifferent php5Vars [1, 2, 3, 4]).filterMap normalize)
      (fun a _ => (php5Vars.map a).Nodup)
      (fun _ _ _ => false)
    · intro a' bA hdom' hnodup' c hc
      exact extend_sat_encodeAllDifferent a' bA _ hdom' php5Vars [1, 2, 3, 4] c hc hnodup'
    · exact php5_formulaUnsat
  exact key ⟨a, fun _ => false, hdom, hnodup⟩

/-! ### Scaling checkpoints: `php_7_6` and `php_9_8`

Two larger pigeonhole instances, committed as scaling checkpoints for the
verified-PB cutting-planes pipeline (see `docs/SCALING.md`).  Pigeonhole is
exponentially hard for resolution (Haken 1985) but has polynomial cutting-planes
refutations; the verified kernel certificate here grows linearly in the number of
holes (php_3_2: 168 chars, php_5_4: 221, php_7_6: 269, php_9_8: 317), in stark
contrast to the resolution (DRAT) proofs of the same instances, which blow up
exponentially.  The proof structure is identical to `php_5_4` above — only the
instance size, domain, value list, and certificate change. -/

/-- The PB signature for `php_7_6`: seven integer variables over `{1,…,6}`. -/
def php7Sig : CSPSig where
  nInt := 7
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 6
  sorted := fun _ => domainValues_sorted 1 6
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The pigeon variables as the scope of the corpus `alldifferent`. -/
def php7Scope : _root_.Vector (HomogeneousVarIndex 7) 7 := _root_.Vector.ofFn id

/-- The pigeon variable list (the `alldifferent` scope as a `List`). -/
def php7Vars : List (Fin php7Sig.nInt) := php7Scope.toList

/-- The PB encoding of `php_7_6`: staircase clauses plus the normalized
    `alldifferent` per-value constraints over the shared domain `{1,…,6}`. -/
def php7Encoded : List (PBConstr (PBVar php7Sig)) :=
  php7Sig.monotonicity ++ (encodeAllDifferent php7Vars [1, 2, 3, 4, 5, 6]).filterMap normalize

/-- The veripb-elaborated kernel proof of UNSAT for `php7Encoded`'s OPB
    serialization (RoundingSat + veripb; both untrusted). The 35 thresholds map to
    OPB `x1,…,x35`. -/
def php7KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 34;
rup >= 0 : ~ ;
pol 35 29 1000000000000000 * + 30 1000000000000000 * + 31 1000000000000000 * + 32 1000000000000000 * + 33 1000000000000000 * + 34 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 36;
end pseudo-Boolean proof;
"

/-- The PB encoding of `php_7_6` is unsatisfiable — kernel-checked through PBLean's
    verified reflection checker (`native_decide`; RoundingSat / veripb / serializer
    untrusted). -/
theorem php7_formulaUnsat :
    VeriPB.Reflect.formulaUnsat (php7Encoded.toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 35 php7KernelProof (by native_decide)

/-- **End-to-end pigeonhole UNSAT (`php_7_6`).** Seven pigeons into six holes,
    `alldifferent`, via the same verified PB pipeline as `php_3_2` / `php_5_4`. -/
theorem php_7_6_unsat : ¬ php_7_6.isSatisfiable := by
  rintro ⟨a, hsol⟩
  have hdom : ∀ i : Fin php7Sig.nInt, a i ∈ php7Sig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (6 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (6 : ℕ) a hb
    have h2' : a i ≤ 6 := by exact_mod_cast h2
    show a i ∈ domainValues 1 6
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  have hnodup : (php7Vars.map a).Nodup := by
    have ha : HomogeneousCSP.satisfiesConstraint (php_alldiff 7) a :=
      hsol _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    exact alldifferent_sat php7Scope a ha
  have key : ¬ ∃ (a : Fin php7Sig.nInt → Int) (_ : Fin php7Sig.nBool → Bool),
      (∀ i, a i ∈ php7Sig.values i) ∧ (php7Vars.map a).Nodup := by
    apply csp_unsat_generic php7Sig
      ((encodeAllDifferent php7Vars [1, 2, 3, 4, 5, 6]).filterMap normalize)
      (fun a _ => (php7Vars.map a).Nodup)
      (fun _ _ _ => false)
    · intro a' bA hdom' hnodup' c hc
      exact extend_sat_encodeAllDifferent a' bA _ hdom' php7Vars [1, 2, 3, 4, 5, 6] c hc hnodup'
    · exact php7_formulaUnsat
  exact key ⟨a, fun _ => false, hdom, hnodup⟩

/-- The PB signature for `php_9_8`: nine integer variables over `{1,…,8}`. -/
def php9Sig : CSPSig where
  nInt := 9
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 8
  sorted := fun _ => domainValues_sorted 1 8
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The pigeon variables as the scope of the corpus `alldifferent`. -/
def php9Scope : _root_.Vector (HomogeneousVarIndex 9) 9 := _root_.Vector.ofFn id

/-- The pigeon variable list (the `alldifferent` scope as a `List`). -/
def php9Vars : List (Fin php9Sig.nInt) := php9Scope.toList

/-- The PB encoding of `php_9_8`: staircase clauses plus the normalized
    `alldifferent` per-value constraints over the shared domain `{1,…,8}`. -/
def php9Encoded : List (PBConstr (PBVar php9Sig)) :=
  php9Sig.monotonicity ++ (encodeAllDifferent php9Vars [1, 2, 3, 4, 5, 6, 7, 8]).filterMap normalize

/-- The veripb-elaborated kernel proof of UNSAT for `php9Encoded`'s OPB
    serialization (RoundingSat + veripb; both untrusted). The 63 thresholds map to
    OPB `x1,…,x63`. -/
def php9KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 62;
rup >= 0 : ~ ;
pol 63 55 1000000000000000 * + 56 1000000000000000 * + 57 1000000000000000 * + 58 1000000000000000 * + 59 1000000000000000 * + 60 1000000000000000 * + 61 1000000000000000 * + 62 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 64;
end pseudo-Boolean proof;
"

/-- The PB encoding of `php_9_8` is unsatisfiable — kernel-checked through PBLean's
    verified reflection checker (`native_decide`; RoundingSat / veripb / serializer
    untrusted). -/
theorem php9_formulaUnsat :
    VeriPB.Reflect.formulaUnsat (php9Encoded.toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 63 php9KernelProof (by native_decide)

/-- **End-to-end pigeonhole UNSAT (`php_9_8`).** Nine pigeons into eight holes,
    `alldifferent`, via the same verified PB pipeline as `php_3_2` / `php_5_4`. -/
theorem php_9_8_unsat : ¬ php_9_8.isSatisfiable := by
  rintro ⟨a, hsol⟩
  have hdom : ∀ i : Fin php9Sig.nInt, a i ∈ php9Sig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (8 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (8 : ℕ) a hb
    have h2' : a i ≤ 8 := by exact_mod_cast h2
    show a i ∈ domainValues 1 8
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  have hnodup : (php9Vars.map a).Nodup := by
    have ha : HomogeneousCSP.satisfiesConstraint (php_alldiff 9) a :=
      hsol _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    exact alldifferent_sat php9Scope a ha
  have key : ¬ ∃ (a : Fin php9Sig.nInt → Int) (_ : Fin php9Sig.nBool → Bool),
      (∀ i, a i ∈ php9Sig.values i) ∧ (php9Vars.map a).Nodup := by
    apply csp_unsat_generic php9Sig
      ((encodeAllDifferent php9Vars [1, 2, 3, 4, 5, 6, 7, 8]).filterMap normalize)
      (fun a _ => (php9Vars.map a).Nodup)
      (fun _ _ _ => false)
    · intro a' bA hdom' hnodup' c hc
      exact extend_sat_encodeAllDifferent a' bA _ hdom' php9Vars
        [1, 2, 3, 4, 5, 6, 7, 8] c hc hnodup'
    · exact php9_formulaUnsat
  exact key ⟨a, fun _ => false, hdom, hnodup⟩

end CSP.L2S.PB.Pigeonhole
