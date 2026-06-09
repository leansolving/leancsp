import CSP.L2S.Backends.PB.CircuitGates
import CSP.L2S.Backends.PB.LinearNe
import CSP.L2S.Tests.lean.«29_ripple_carry_adder»

namespace CSP.L2S.PB.RippleCarry

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for a 4-bit ripple-carry adder

This **scales the full-adder verification** (`FullAdder.lean`) to the 4-bit
ripple-carry adder of `Tests/lean/29_ripple_carry_adder.lean`: four chained full
adders (29 variables, 22 constraints), again with **no `BoolExpr` compiler** — the
same per-stage full-adder identity, applied four times, suffices.

Each stage `i` computes `aᵢ + bᵢ + cᵢ = sᵢ + 2·cᵢ₊₁` (`fa_identity` from
`CircuitGates.lean`), the carry-in `c0` is pinned to `0`, and the corpus asserts the
**negated** correctness property `A + B ≠ Σ 2ⁱsᵢ + 16·cout`.  Multiplying stage `i`'s
identity by `2ⁱ` and summing, the intermediate carries `2c1+4c2+8c3` telescope away,
leaving exactly `A + B - Result = 0` — the negation of the asserted violation.  So the
CSP is unsatisfiable (the adder is correct).

The proof flattens the solution hypothesis over all 22 constraints at once
(`List.forall_mem_append`/`_cons`), extracts each stage's gate semantics via the shared
`xor_all3_sat` / `and_gate_sat` / `or_all3_full_sat` bridges, obtains the four stage
identities, and combines them with `linarith` (the carries cancel).  The negated
property gives `L ≠ 0` via `linear_ne_sat`; the contradiction rides the generic spine
`csp_unsat_generic` (linear `≤` halves + Big-M `encodeLinearNe`) and the committed PB
certificate.
-/

/-! ### The signature and PB encoding -/

/-- The PB signature: the 29 `{0,1}` variables of the 4-bit adder, plus one selector
    auxiliary for the Big-M disequality of the negated property. -/
def rcSig : CSPSig where
  nInt := 29
  nBool := 0
  nAux := 1
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The correctness linear form `L = A + B - Result`
    `= Σ 2ⁱaᵢ + Σ 2ⁱbᵢ - Σ 2ⁱsᵢ - 16·cout` (matching the corpus violation's coefficients). -/
def rcTerms : List (Int × Fin rcSig.nInt) :=
  [(1, (0:Fin 29)), (2, (1:Fin 29)), (4, (2:Fin 29)), (8, (3:Fin 29)),
   (1, (4:Fin 29)), (2, (5:Fin 29)), (4, (6:Fin 29)), (8, (7:Fin 29)),
   (-1, (8:Fin 29)), (-2, (9:Fin 29)), (-4, (10:Fin 29)), (-8, (11:Fin 29)),
   (-16, (16:Fin 29))]

/-- The negated form `-L` (for the `L ≥ 0` half). -/
def rcTermsNeg : List (Int × Fin rcSig.nInt) :=
  [(-1, (0:Fin 29)), (-2, (1:Fin 29)), (-4, (2:Fin 29)), (-8, (3:Fin 29)),
   (-1, (4:Fin 29)), (-2, (5:Fin 29)), (-4, (6:Fin 29)), (-8, (7:Fin 29)),
   (1, (8:Fin 29)), (2, (9:Fin 29)), (4, (10:Fin 29)), (8, (11:Fin 29)),
   (16, (16:Fin 29))]

/-- `L` evaluated on an assignment. -/
theorem rcSum (a : Fin rcSig.nInt → Int) :
    (rcTerms.map (fun p => p.1 * a p.2)).sum
      = a (0:Fin 29) + 2 * a (1:Fin 29) + 4 * a (2:Fin 29) + 8 * a (3:Fin 29)
        + a (4:Fin 29) + 2 * a (5:Fin 29) + 4 * a (6:Fin 29) + 8 * a (7:Fin 29)
        - a (8:Fin 29) - 2 * a (9:Fin 29) - 4 * a (10:Fin 29) - 8 * a (11:Fin 29)
        - 16 * a (16:Fin 29) := by
  simp only [rcTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- `-L` evaluated on an assignment. -/
theorem rcSumNeg (a : Fin rcSig.nInt → Int) :
    (rcTermsNeg.map (fun p => p.1 * a p.2)).sum
      = -(a (0:Fin 29) + 2 * a (1:Fin 29) + 4 * a (2:Fin 29) + 8 * a (3:Fin 29)
        + a (4:Fin 29) + 2 * a (5:Fin 29) + 4 * a (6:Fin 29) + 8 * a (7:Fin 29)
        - a (8:Fin 29) - 2 * a (9:Fin 29) - 4 * a (10:Fin 29) - 8 * a (11:Fin 29)
        - 16 * a (16:Fin 29)) := by
  simp only [rcTermsNeg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- The selector auxiliary set from a solution: records whether `L` exceeds `0`. -/
def rcAux (a : Fin rcSig.nInt → Int) (_ : Fin rcSig.nBool → Bool) : Fin rcSig.nAux → Bool :=
  fun _ => decide ((rcTerms.map (fun p => p.1 * a p.2)).sum > 0)

/-- The PB user constraints: the identity `L = 0` as the linear pair `L ≤ 0`, `L ≥ 0`,
    and the negated property `L ≠ 0` as the Big-M `encodeLinearNe` (one selector aux). -/
def rcUser : List (PBConstr (PBVar rcSig)) :=
  (normalize (encodeLinearLe rcTerms 0)).toList ++
  (normalize (encodeLinearLe rcTermsNeg 0)).toList ++
  ((encodeLinearNe rcTerms 0 (0 : Fin 1)).filterMap normalize)

/-- The veripb-elaborated kernel proof of UNSAT for `rcUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The 29 width-1 variables map to OPB
    `x1..x29` (`a i ≤ 0` of variable `i` is `x{i+1}`); the selector aux is `x30`.  Only
    the input/output thresholds `x1..x12, x17` and the selector `x30` appear — the carry
    and AND-gate variables were folded into the per-stage identities. -/
def rcKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 4;
rup >= 0 : ~ ;
pol 3 s;
pol 4 s;
pbc 1000000000000000 x9 1000000000000000 x10 1000000000000000 x11 1000000000000000 x12 1000000000000000 x17 >= 1000000000000000 : subproof
rup 1000000000000000 x1 2000000000000000 x2 4000000000000000 x3 8000000000000000 x4 1000000000000000 x5 2000000000000000 x6 4000000000000000 x7 8000000000000000 x8 >= 0 : ~ ;
pol 8 2 1000000000000000 * + 9 + 15000000000000000 d;
pol 8 10 1000000000000000 * +;
qed : 11;
pbc 1000000000000000 x9 1000000000000000 x10 1000000000000000 x11 1000000000000000 x12 1000000000000000 x17 >= 1000000000000000 : subproof
pol 13 1000000000000000 d;
pol 13 14 15000000000000000 * + 2 1000000000000000 * +;
qed : 15;
pbc 1000000000000000 x30 >= 1000000000000000 : subproof
pol 17 2 1000000000000000 * + 6 1000000000000000 * + 30000000000000000 d;
pol 17 18 1000000000000000 * +;
qed : 19;
pbc 1000000000000000 x30 >= 1000000000000000 : subproof
pol 21 1000000000000000 d;
pol 21 22 30000000000000000 * + 2 1000000000000000 * + 6 1000000000000000 * +;
qed : 23;
pbc 1 x1 2 x2 4 x3 8 x4 1 x5 2 x6 4 x7 8 x8 31249999999999 x30 >= 31249999999999 : subproof
rup 1 x9 2 x10 4 x11 8 x12 16 x17 >= 0 : ~ ;
pol 25 2 31249999999999 * + 6 31250000000000 * + 26 + 937500000000001 d;
pol 25 27 31249999999999 * +;
qed : 28;
pbc 1 x1 2 x2 4 x3 8 x4 1 x5 2 x6 4 x7 8 x8 31249999999999 x30 >= 31249999999999 : subproof
rup 1 x1 2 x2 4 x3 8 x4 1 x5 2 x6 4 x7 8 x8 >= 0 : ~ ;
pol 30 31 + 31249999999999 d;
pol 30 32 937500000000001 * + 2 31249999999999 * + 6 31250000000000 * +;
qed : 33;
pol 12 1000000000000000 d;
pol 20 1000000000000000 d;
pol 20 1000000000000000 d;
pol 12 1000000000000000 d;
pol 5 1 31250000000000 * + 7 31250000000000 * + 36 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 39;
end pseudo-Boolean proof;
"

/-- The PB encoding of the ripple-carry-adder verification query is unsatisfiable —
    established by the external PB certificate, kernel-checked through PBLean's verified
    reflection checker (`native_decide` runs the checker; RoundingSat / veripb / the
    serializer are untrusted). -/
theorem rc_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((rcSig.monotonicity ++ rcUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 30 rcKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain `{0,1}` assignment with `L = 0` yet `L ≠ 0`. -/
theorem rc_no_sol : ¬ ∃ (a : Fin rcSig.nInt → Int) (_ : Fin rcSig.nBool → Bool),
    (∀ i, a i ∈ rcSig.values i) ∧
    (((rcTerms.map (fun p => p.1 * a p.2)).sum = 0) ∧
     ((rcTerms.map (fun p => p.1 * a p.2)).sum ≠ 0)) := by
  apply csp_unsat_generic rcSig rcUser
    (fun a _ => ((rcTerms.map (fun p => p.1 * a p.2)).sum = 0) ∧
      ((rcTerms.map (fun p => p.1 * a p.2)).sum ≠ 0))
    rcAux
  · intro a bA hdom hP c hc
    obtain ⟨hL0, hLne⟩ := hP
    unfold rcUser at hc
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA (rcAux a bA) hdom rcTerms 0 c hc ?_
      omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA (rcAux a bA) hdom rcTermsNeg 0 c hc ?_
      rw [rcSumNeg]; rw [rcSum] at hL0; omega
    · exact extend_sat_encodeLinearNe a bA (rcAux a bA) hdom rcTerms 0 (0:Fin 1) hLne rfl c hc
  · exact rc_formulaUnsat

/-- **End-to-end 4-bit ripple-carry-adder UNSAT.** The corpus CSP
    `ripple_carry_adder_4bit` — assert the adder violates `A + B = Result` — is
    unsatisfiable (the adder is correct), discharged through the verified PB pipeline:
    the four stage identities (`fa_identity` per full adder) combine (carries cancel) to
    `L = 0`, the negated-property `linear_ne` bridge gives `L ≠ 0`, and the committed
    certificate `rc_formulaUnsat` closes it.  **No `BoolExpr` compiler.** -/
theorem ripple_carry_4bit_correct_unsat : ¬ ripple_carry_adder_4bit.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Flatten the solution hypothesis into one named fact per constraint.
  unfold IntCSP.isSolutionInt ripple_carry_adder_4bit at hsol
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    List.forall_mem_append, List.forall_mem_cons] at hsol
  obtain ⟨hbounds, hc0, hs0sum, hs0ab, hs0ac, hs0bc, hs0cout,
    hs1sum, hs1ab, hs1ac, hs1bc, hs1cout,
    hs2sum, hs2ab, hs2ac, hs2bc, hs2cout,
    hs3sum, hs3ab, hs3ac, hs3bc, hs3cout, hviol, _⟩ := hsol
  -- Every variable lies in `{0,1}` (from its `bound`).
  have hdom : ∀ i : Fin rcSig.nInt, a i ∈ rcSig.values i := by
    intro i
    obtain ⟨h1, h2⟩ := bound_sat i 0 1 a
      (hbounds (bound i 0 1) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))
    exact mem_domainValues.mpr ⟨h1, h2⟩
  -- Domain bounds for the stage inputs and carries.
  have d0 := mem_domainValues.mp (hdom (0:Fin 29)); have d1 := mem_domainValues.mp (hdom (1:Fin 29))
  have d2 := mem_domainValues.mp (hdom (2:Fin 29)); have d3 := mem_domainValues.mp (hdom (3:Fin 29))
  have d4 := mem_domainValues.mp (hdom (4:Fin 29)); have d5 := mem_domainValues.mp (hdom (5:Fin 29))
  have d6 := mem_domainValues.mp (hdom (6:Fin 29)); have d7 := mem_domainValues.mp (hdom (7:Fin 29))
  have d12 := mem_domainValues.mp (hdom (12:Fin 29))
  have d13 := mem_domainValues.mp (hdom (13:Fin 29))
  have d14 := mem_domainValues.mp (hdom (14:Fin 29))
  have d15 := mem_domainValues.mp (hdom (15:Fin 29))
  -- The four full-adder stage identities.
  have hS0 : a (0:Fin 29) + a (4:Fin 29) + a (12:Fin 29) - a (8:Fin 29) - 2 * a (13:Fin 29) = 0 :=
    fa_identity _ _ _ _ _ _ _ _ d0.1 d0.2 d4.1 d4.2 d12.1 d12.2
      (xor_all3_sat _ _ _ _ a hs0sum) (and_gate_sat _ _ _ a hs0ab)
      (and_gate_sat _ _ _ a hs0ac) (and_gate_sat _ _ _ a hs0bc)
      (or_all3_full_sat _ _ _ _ a hs0cout)
  have hS1 : a (1:Fin 29) + a (5:Fin 29) + a (13:Fin 29) - a (9:Fin 29) - 2 * a (14:Fin 29) = 0 :=
    fa_identity _ _ _ _ _ _ _ _ d1.1 d1.2 d5.1 d5.2 d13.1 d13.2
      (xor_all3_sat _ _ _ _ a hs1sum) (and_gate_sat _ _ _ a hs1ab)
      (and_gate_sat _ _ _ a hs1ac) (and_gate_sat _ _ _ a hs1bc)
      (or_all3_full_sat _ _ _ _ a hs1cout)
  have hS2 : a (2:Fin 29) + a (6:Fin 29) + a (14:Fin 29) - a (10:Fin 29) - 2 * a (15:Fin 29) = 0 :=
    fa_identity _ _ _ _ _ _ _ _ d2.1 d2.2 d6.1 d6.2 d14.1 d14.2
      (xor_all3_sat _ _ _ _ a hs2sum) (and_gate_sat _ _ _ a hs2ab)
      (and_gate_sat _ _ _ a hs2ac) (and_gate_sat _ _ _ a hs2bc)
      (or_all3_full_sat _ _ _ _ a hs2cout)
  have hS3 : a (3:Fin 29) + a (7:Fin 29) + a (15:Fin 29) - a (11:Fin 29) - 2 * a (16:Fin 29) = 0 :=
    fa_identity _ _ _ _ _ _ _ _ d3.1 d3.2 d7.1 d7.2 d15.1 d15.2
      (xor_all3_sat _ _ _ _ a hs3sum) (and_gate_sat _ _ _ a hs3ab)
      (and_gate_sat _ _ _ a hs3ac) (and_gate_sat _ _ _ a hs3bc)
      (or_all3_full_sat _ _ _ _ a hs3cout)
  -- Carry-in `c0 = 0`.
  have hC0 : a (12:Fin 29) = 0 := equals_const_sat _ 0 a hc0
  -- Combine: `L = 0` (the intermediate carries cancel).
  have hL0 : (rcTerms.map (fun p => p.1 * a p.2)).sum = 0 := by
    rw [rcSum]; linarith [hS0, hS1, hS2, hS3, hC0]
  -- The negated correctness property: `L ≠ 0`.
  have hLne : (rcTerms.map (fun p => p.1 * a p.2)).sum ≠ 0 := by
    have hne := linear_ne_sat
      (⟨#[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
         ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩,
         ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩,
         ⟨16, by decide⟩], rfl⟩ : _root_.Vector (Fin 29) 13)
      (⟨#[1, 2, 4, 8, 1, 2, 4, 8, -1, -2, -4, -8, -16], rfl⟩) 0 a hviol
    rw [rcSum]; simp at hne; intro hC; exact hne (by linarith)
  exact rc_no_sol ⟨a, fun _ => false, hdom, hL0, hLne⟩

end CSP.L2S.PB.RippleCarry
