import CSP.L2S.Backends.PB.CircuitGates
import CSP.L2S.Backends.PB.LinearNe
import CSP.L2S.Tests.lean.«28_full_adder_verification»

namespace CSP.L2S.PB.FullAdder

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for full-adder circuit verification

This verifies the **full-adder circuit** of `Tests/lean/28_full_adder_verification.lean`
through the PB pipeline, and is the **first circuit consumer using a 3-input XOR** —
the gate that earlier sessions flagged as blocked, supposedly needing the recursive
`BoolExpr` Tseitin compiler (`BoolExprCompiler.lean`, task #41 part 3).  It does **not**:
a 3-input XOR over `{0,1}` is captured by the full-adder *identity* below, exactly as a
2-input XOR turned out to be linear (`CircuitEquiv.lean`).  So the PB pipeline reaches
the parity-circuit family with **no new compiler infrastructure**.

The corpus CSP fixes inputs `a=v0, b=v1, cin=v2`, computes `sum=v3` by `xor_all [v0,v1,v2]`
and `cout=v4` by `or_all [ab,ac,bc]` over the AND gates `ab=v5,ac=v6,bc=v7`, then asserts
the **negated** correctness property `v0+v1+v2 - 2·v4 - v3 ≠ 0`.  A full adder is correct,
so the CSP is unsatisfiable.

The proof extracts the gate semantics (the reusable `xor_all3_sat` / `and_gate_sat` /
`or_all3_full_sat` bridges in `CircuitGates.lean`) and combines them with the arithmetic
identity `a + b + cin = sum + 2·cout` (the pure-`ℤ` `fa_identity`, also in
`CircuitGates.lean`):

* `xor_all3_sat` — `sum = parity`, i.e. `(v0+v1+v2) % 2 = v3`;
* `and_gate_sat` — each AND output is the `min` of its inputs;
* `or_all3_full_sat` — `cout = max(ab,ac,bc)`;
* `fa_identity` — a pure-`ℤ` `{0,1}³` enumeration giving `v0+v1+v2 - v3 - 2·v4 = 0`;
* `linear_ne_sat` — the negated property gives `v0+v1+v2 - v3 - 2·v4 ≠ 0`.

The two facts contradict, routed through the generic spine `csp_unsat_generic`: the
identity is encoded as the linear pair `L ≤ 0`, `L ≥ 0` and the negated property as the
Big-M `encodeLinearNe` (one selector aux), and the committed PB certificate closes it.
-/

/-! ### The signature and PB encoding -/

/-- The PB signature: the eight `{0,1}` circuit variables, plus one Boolean-style
    selector auxiliary for the Big-M disequality of the negated property. -/
def faSig : CSPSig where
  nInt := 8
  nBool := 0
  nAux := 1
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The linear form `L = v0 + v1 + v2 - v3 - 2·v4` of the correctness identity. -/
def faTerms : List (Int × Fin faSig.nInt) :=
  [(1, (0:Fin 8)), (1, (1:Fin 8)), (1, (2:Fin 8)), (-1, (3:Fin 8)), (-2, (4:Fin 8))]

/-- The negated form `-L` (for the `L ≥ 0` half). -/
def faTermsNeg : List (Int × Fin faSig.nInt) :=
  [(-1, (0:Fin 8)), (-1, (1:Fin 8)), (-1, (2:Fin 8)), (1, (3:Fin 8)), (2, (4:Fin 8))]

/-- `L` evaluated on an assignment is `a 0 + a 1 + a 2 - a 3 - 2·a 4`. -/
theorem faSum (a : Fin faSig.nInt → Int) :
    (faTerms.map (fun p => p.1 * a p.2)).sum
      = a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8) := by
  simp only [faTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- `-L` evaluated on an assignment. -/
theorem faSumNeg (a : Fin faSig.nInt → Int) :
    (faTermsNeg.map (fun p => p.1 * a p.2)).sum
      = -(a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8)) := by
  simp only [faTermsNeg, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- The selector auxiliary set from a solution: records whether `L` exceeds `0`, as
    `encodeLinearNe`'s soundness requires. -/
def faAux (a : Fin faSig.nInt → Int) (_ : Fin faSig.nBool → Bool) : Fin faSig.nAux → Bool :=
  fun _ => decide ((faTerms.map (fun p => p.1 * a p.2)).sum > 0)

/-- The PB user constraints: the identity `L = 0` as the linear pair `L ≤ 0`, `L ≥ 0`,
    and the negated property `L ≠ 0` as the Big-M `encodeLinearNe` (one selector aux). -/
def faUser : List (PBConstr (PBVar faSig)) :=
  (normalize (encodeLinearLe faTerms 0)).toList ++
  (normalize (encodeLinearLe faTermsNeg 0)).toList ++
  ((encodeLinearNe faTerms 0 (0 : Fin 1)).filterMap normalize)

/-- The veripb-elaborated kernel proof of UNSAT for `faUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The eight width-1 variables map to OPB
    `x1..x8` (`a i ≤ 0` of variable `i` is `x{i+1}`); the selector aux is `x9`.  Only
    `x1..x5` (inputs/sum/cout) and `x9` appear — the AND outputs `x6..x8` were folded
    into the identity. -/
def faKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 4;
rup >= 0 : ~ ;
pol 3 s;
pol 4 s;
pbc 1000000000000000 x1 1000000000000000 x2 1000000000000000 x3 1000000000000000 x9 >= 1000000000000000 : subproof
rup 1000000000000000 x4 2000000000000000 x5 >= 0 : ~ ;
pol 8 6 1000000000000000 * + 9 + 3000000000000000 d;
pol 8 10 1000000000000000 * +;
qed : 11;
pbc 1000000000000000 x1 1000000000000000 x2 1000000000000000 x3 1000000000000000 x9 >= 1000000000000000 : subproof
pol 13 1000000000000000 d;
pol 13 14 3000000000000000 * + 6 1000000000000000 * +;
qed : 15;
pol 12 1000000000000000 d;
pol 12 1000000000000000 d;
rup 1 x4 2 x5 >= 0 : ~;
pol 7 6 19 + 4 d 4 * + s 1 + x5 + s;
rup 1 x1 1 x2 1 ~x4 >= 0 : ~;
rup 1 ~x3 1 x4 >= 0 : ~;
pol 6 7 21 + 4 d 4 * + s 2 + s 20 + 1 22 + 2 d + s;
pol 6 2 + s;
pol 5 1 1000000000000000 * + 7 1000000000000000 * + 24 4000000000000000 * +;
output NONE ;
conclusion UNSAT : 25;
end pseudo-Boolean proof;
"

/-- The PB encoding of the full-adder verification query is unsatisfiable — established
    by the external PB certificate, kernel-checked through PBLean's verified reflection
    checker (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem fa_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((faSig.monotonicity ++ faUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 9 faKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain `{0,1}` assignment for which the identity
    `L = 0` holds yet the negated property `L ≠ 0` also holds (`L = v0+v1+v2 - v3 - 2·v4`). -/
theorem fa_no_sol : ¬ ∃ (a : Fin faSig.nInt → Int) (_ : Fin faSig.nBool → Bool),
    (∀ i, a i ∈ faSig.values i) ∧
    ((a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8) = 0) ∧
     (a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8) ≠ 0)) := by
  apply csp_unsat_generic faSig faUser
    (fun a _ => (a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8) = 0) ∧
      (a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8) ≠ 0))
    faAux
  · intro a bA hdom hP c hc
    obtain ⟨hL0, hLne⟩ := hP
    unfold faUser at hc
    rw [List.mem_append, List.mem_append] at hc
    rcases hc with (hc | hc) | hc
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA (faAux a bA) hdom faTerms 0 c hc ?_
      rw [faSum]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA (faAux a bA) hdom faTermsNeg 0 c hc ?_
      rw [faSumNeg]; omega
    · refine extend_sat_encodeLinearNe a bA (faAux a bA) hdom faTerms 0 (0:Fin 1) ?_ rfl c hc
      rw [faSum]; exact hLne
  · exact fa_formulaUnsat

/-- **End-to-end full-adder-verification UNSAT.** The corpus CSP
    `full_adder_verification` — assert a full adder violates its correctness property
    `a + b + cin = sum + 2·cout` — is unsatisfiable (the adder is correct), discharged
    through the verified PB pipeline: the XOR / AND / OR gate bridges plus the
    `{0,1}³` identity `fa_identity` give `L = 0`, the negated-property `linear_ne`
    bridge gives `L ≠ 0`, the generic spine `csp_unsat_generic` turns those into a PB
    model (linear `≤` halves + Big-M `≠`), and the committed certificate
    `fa_formulaUnsat` contradicts it.  **The 3-input XOR needs no `BoolExpr` compiler.** -/
theorem full_adder_correct_unsat : ¬ full_adder_verification.isSatisfiable := by
  rintro ⟨a, hsol⟩
  -- Every circuit variable lies in `{0,1}` (from its `bound`).
  have hdom : ∀ i : Fin faSig.nInt, a i ∈ faSig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 0 1) a := by
      apply hsol
      show bound i 0 1 ∈ full_adder_verification.constraints
      unfold full_adder_verification
      simp only []
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 0 1 a hb
    show a i ∈ domainValues 0 1
    exact mem_domainValues.mpr ⟨h1, h2⟩
  -- Domain bounds for the three inputs (for the identity enumeration).
  have hd0 := mem_domainValues.mp (hdom (0:Fin 8))
  have hd1 := mem_domainValues.mp (hdom (1:Fin 8))
  have hd2 := mem_domainValues.mp (hdom (2:Fin 8))
  -- The gate semantics (`sum = parity`, AND outputs = `min`, `cout = max`).
  have hx : (a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8)) % 2 = a (3:Fin 8) :=
    xor_all3_sat _ _ _ _ a (by
      apply hsol; show _ ∈ full_adder_verification.constraints
      unfold full_adder_verification; simp only []
      apply List.mem_append_right; exact List.mem_cons_self)
  have h5 : a (5:Fin 8) = min (a (0:Fin 8)) (a (1:Fin 8)) :=
    and_gate_sat _ _ _ a (by
      apply hsol; show _ ∈ full_adder_verification.constraints
      unfold full_adder_verification; simp only []
      apply List.mem_append_right; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have h6 : a (6:Fin 8) = min (a (0:Fin 8)) (a (2:Fin 8)) :=
    and_gate_sat _ _ _ a (by
      apply hsol; show _ ∈ full_adder_verification.constraints
      unfold full_adder_verification; simp only []
      apply List.mem_append_right
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have h7 : a (7:Fin 8) = min (a (1:Fin 8)) (a (2:Fin 8)) :=
    and_gate_sat _ _ _ a (by
      apply hsol; show _ ∈ full_adder_verification.constraints
      unfold full_adder_verification; simp only []
      apply List.mem_append_right
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have h4 : a (4:Fin 8) = max (max (a (5:Fin 8)) (a (6:Fin 8))) (a (7:Fin 8)) :=
    or_all3_full_sat _ _ _ _ a (by
      apply hsol; show _ ∈ full_adder_verification.constraints
      unfold full_adder_verification; simp only []
      apply List.mem_append_right
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))
  -- The correctness identity `L = 0`.
  have hL0 : a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8) = 0 :=
    fa_identity _ _ _ _ _ _ _ _ hd0.1 hd0.2 hd1.1 hd1.2 hd2.1 hd2.2 hx h5 h6 h7 h4
  -- The negated correctness property `L ≠ 0`.
  have hLne : a (0:Fin 8) + a (1:Fin 8) + a (2:Fin 8) - a (3:Fin 8) - 2 * a (4:Fin 8) ≠ 0 := by
    have hne := linear_ne_sat
      (⟨#[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩], rfl⟩ :
        _root_.Vector (Fin 8) 5)
      (⟨#[1, 1, 1, -2, -1], rfl⟩) 0 a (by
        apply hsol; show _ ∈ full_adder_verification.constraints
        unfold full_adder_verification; simp only []
        apply List.mem_append_right
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
    simp at hne
    intro hC; exact hne (by linarith)
  exact fa_no_sol ⟨a, fun _ => false, hdom, hL0, hLne⟩

end CSP.L2S.PB.FullAdder
