import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«32_circuit_at_least»

namespace CSP.L2S.PB.Circuit

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for a circuit-verification corpus CSP

This is the **first circuit-verification consumer** of the PB pipeline.  The
corpus CSP `at_least_k_satisfies_circuit_csp majority3_circuit 2`
(`Tests/lean/32_circuit_at_least.lean`) asks: is there an input with *at least 2*
of `{A,B,C}` set, on which the 3-input **majority** circuit (the full-adder CARRY,
`CARRY = AB ∨ BC ∨ AC`) outputs `0`?  It is **unsatisfiable** — i.e. ≥2 inputs ⇒
`CARRY = 1` — which is exactly the carry-correctness property.

The circuit is built from `and_all` / `or_all` gates over the Boolean domain
`{0,1}`.  The key observation that keeps this in the **linear** PB fragment (no
Boolean/Tseitin machinery, no aux) is that over `{0,1}`:

* `result = AND(x,y)` (`= min`) implies the linear lower bound `x + y - 1 ≤ result`;
* `result = OR(g₁,g₂,g₃)` (`= max`) implies `gᵢ ≤ result` (the `le_max` direction).

Those consequences, together with the cardinality `A + B + C ≥ 2` (`at_least_k`)
and `CARRY ≠ 1` (`not_equals_const`), are already unsatisfiable: from `CARRY = 0`
every `gᵢ = 0`, so each input pair has a `0`, so at most one input is `1`,
contradicting `≥ 2`.  All eight facts are linear / `≠`-const, so the proof rides the
existing `encodeLinearLe` + `encodeNeConst` encoders through the generic spine
`csp_unsat_generic` (aux-free) — the AND/OR gates need **no** BoolExpr compiler.

The builder `at_least_k_satisfies_circuit_csp majority3_circuit 2` reduces
definitionally to its explicit constraint list, so corpus-constraint membership is
direct (no `filterMap`/`foldl` navigation).
-/

/-- The PB signature: seven Boolean nodes (`A,B,C`, the three AND gates `g₁,g₂,g₃`,
    and `CARRY`), each over the domain `{0,1}`, no Booleans or auxiliaries. -/
def circSig : CSPSig where
  nInt := 7
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-! ### Corpus bridges: gates and cardinality become linear facts -/

/-- **Bridge.** A satisfied binary `and_all [x,y] r` over `{0,1}` (`r = min(x,y)`)
    gives the AND lower bound `a x + a y - 1 ≤ a r` (uses the domain upper bounds).
    The `foldl`-min checker is reduced to the `min`-`if`, then `split_ifs` + `linarith`. -/
theorem and_all2_lower_sat (x y r : Fin 7) (a : IntAssignment 7)
    (hx : a x ≤ 1) (hy : a y ≤ 1)
    (h : IntCSP.satisfiesConstraintInt
      (and_all (⟨#[x, y], rfl⟩ : _root_.Vector (VarType 7) 2) r) a) :
    a x + a y - 1 ≤ a r := by
  simp only [IntCSP.satisfiesConstraintInt, and_all, patternHolds, map_valAt, valAt_eq] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.headI,
    List.foldl_cons, List.foldl_nil, ne_eq] at h
  split_ifs at h <;> linarith

/-- **Bridge.** A satisfied ternary `or_all [g₁,g₂,g₃] r` over `{0,1}` (`r = max`)
    gives the OR lower bounds `gᵢ ≤ a r` (the `le_max` direction; no domain needed). -/
theorem or_all3_le_sat (g1 g2 g3 r : Fin 7) (a : IntAssignment 7)
    (h : IntCSP.satisfiesConstraintInt
      (or_all (⟨#[g1, g2, g3], rfl⟩ : _root_.Vector (VarType 7) 3) r) a) :
    a g1 ≤ a r ∧ a g2 ≤ a r ∧ a g3 ≤ a r := by
  simp only [IntCSP.satisfiesConstraintInt, or_all, patternHolds, map_valAt, valAt_eq] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.headI,
    List.foldl_cons, List.foldl_nil, ne_eq] at h
  split_ifs at h <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- **Bridge.** A satisfied ternary `at_least_k [x,y,z] 2` gives `a x + a y + a z ≥ 2`. -/
theorem at_least3_2_sat (x y z : Fin 7) (a : IntAssignment 7)
    (h : IntCSP.satisfiesConstraintInt
      (at_least_k (⟨#[x, y, z], rfl⟩ : _root_.Vector (VarType 7) 3) 2) a) :
    a x + a y + a z ≥ 2 := by
  simp only [IntCSP.satisfiesConstraintInt, at_least_k, patternHolds, map_valAt] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at h
  push_cast at h
  linarith

/-! ### The PB encoding and certificate -/

/-- The PB user constraints: the linear consequences of the four gates (three AND
    lower bounds `gᵢ ≥ xᵢ + yᵢ - 1`, three OR lower bounds `gᵢ ≤ CARRY`), the
    cardinality `A + B + C ≥ 2`, and `CARRY ≠ 1`.  All aux-free. -/
def circUser : List (PBConstr (PBVar circSig)) :=
  (normalize (encodeLinearLe [(1, (0:Fin 7)), (1, (1:Fin 7)), (-1, (3:Fin 7))] 1)).toList ++
  (normalize (encodeLinearLe [(1, (1:Fin 7)), (1, (2:Fin 7)), (-1, (4:Fin 7))] 1)).toList ++
  (normalize (encodeLinearLe [(1, (0:Fin 7)), (1, (2:Fin 7)), (-1, (5:Fin 7))] 1)).toList ++
  (normalize (encodeLinearLe [(1, (3:Fin 7)), (-1, (6:Fin 7))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (4:Fin 7)), (-1, (6:Fin 7))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (5:Fin 7)), (-1, (6:Fin 7))] 0)).toList ++
  (normalize (encodeLinearLe [(-1, (0:Fin 7)), (-1, (1:Fin 7)), (-1, (2:Fin 7))] (-2))).toList ++
  (normalize (encodeNeConst (6:Fin 7) 1)).toList

/-- The veripb-elaborated kernel proof of UNSAT for `circUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The seven thresholds `a i ≤ 0` map to
    OPB `x1..x7` (so `xᵢ = ⟦node (i-1) = 0⟧`). -/
def circKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 8;
rup >= 0 : ~ ;
rup 1 x4 >= 1 : ~ 8 4;
rup 1 x5 >= 1 : ~ 8 5;
rup 1 x6 >= 1 : ~ 8 6;
rup 500000000000000 x4 500000000000000 x5 500000000000000 x6 >= 1500000000000000 : 10 11 12 ~;
pol 9 1 500000000000000 * + 2 500000000000000 * + 3 500000000000000 * + 7 1000000000000000 * + 13 +;
output NONE ;
conclusion UNSAT : 14;
end pseudo-Boolean proof;
"

/-- The PB encoding of the majority-circuit query is unsatisfiable — established by
    the external PB certificate, kernel-checked through PBLean's verified reflection
    checker (`native_decide` runs the checker; RoundingSat / veripb / the serializer
    are untrusted). -/
theorem circ_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((circSig.monotonicity ++ circUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 7 circKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain Boolean assignment satisfying the
    eight linear / `≠` consequences of the circuit, cardinality, and output
    constraints. -/
theorem circ_no_sol : ¬ ∃ (a : Fin circSig.nInt → Int) (_ : Fin circSig.nBool → Bool),
    (∀ i, a i ∈ circSig.values i) ∧
    ((a (0:Fin 7) + a (1:Fin 7) - 1 ≤ a (3:Fin 7)) ∧
     (a (1:Fin 7) + a (2:Fin 7) - 1 ≤ a (4:Fin 7)) ∧
     (a (0:Fin 7) + a (2:Fin 7) - 1 ≤ a (5:Fin 7)) ∧
     (a (3:Fin 7) ≤ a (6:Fin 7)) ∧ (a (4:Fin 7) ≤ a (6:Fin 7)) ∧ (a (5:Fin 7) ≤ a (6:Fin 7)) ∧
     (a (0:Fin 7) + a (1:Fin 7) + a (2:Fin 7) ≥ 2) ∧ (a (6:Fin 7) ≠ 1)) := by
  apply csp_unsat_generic circSig circUser
    (fun a _ => (a (0:Fin 7) + a (1:Fin 7) - 1 ≤ a (3:Fin 7)) ∧
     (a (1:Fin 7) + a (2:Fin 7) - 1 ≤ a (4:Fin 7)) ∧
     (a (0:Fin 7) + a (2:Fin 7) - 1 ≤ a (5:Fin 7)) ∧
     (a (3:Fin 7) ≤ a (6:Fin 7)) ∧ (a (4:Fin 7) ≤ a (6:Fin 7)) ∧ (a (5:Fin 7) ≤ a (6:Fin 7)) ∧
     (a (0:Fin 7) + a (1:Fin 7) + a (2:Fin 7) ≥ 2) ∧ (a (6:Fin 7) ≠ 1))
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP
    simp only [circUser, List.mem_append] at hc
    rcases hc with ((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (0:Fin 7)), (1, (1:Fin 7)), (-1, (3:Fin 7))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (1:Fin 7)), (1, (2:Fin 7)), (-1, (4:Fin 7))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (0:Fin 7)), (1, (2:Fin 7)), (-1, (5:Fin 7))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (3:Fin 7)), (-1, (6:Fin 7))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (4:Fin 7)), (-1, (6:Fin 7))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (5:Fin 7)), (-1, (6:Fin 7))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(-1, (0:Fin 7)), (-1, (1:Fin 7)), (-1, (2:Fin 7))] (-2) c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      exact extend_sat_encodeNeConst a bA _ hdom (6:Fin 7) 1 h8 c hc
  · exact circ_formulaUnsat

/-- **End-to-end circuit-verification UNSAT.** The corpus CSP
    `at_least_k_satisfies_circuit_csp majority3_circuit 2` — does the 3-input
    majority circuit (full-adder CARRY) output `0` on some input with ≥2 ones? — is
    unsatisfiable, i.e. the carry property "≥2 inputs ⇒ CARRY = 1" holds.  Discharged
    through the verified PB pipeline: the AND/OR gate bridges and the cardinality
    bridge turn any solution into eight linear / `≠` facts, the generic spine
    `csp_unsat_generic` turns those into a PB model via the aux-free `encodeLinearLe`
    / `encodeNeConst` encoders, and the committed certificate `circ_formulaUnsat`
    contradicts it.  No Boolean/Tseitin machinery — AND/OR are linear over `{0,1}`. -/
theorem circuit_majority3_unsat :
    ¬ (at_least_k_satisfies_circuit_csp majority3_circuit 2).isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  have hdom : ∀ i : Fin circSig.nInt, a i ∈ circSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 0 1) a := by
      apply hsol
      show bound i 0 1 ∈ (List.finRange 7).map (fun i => bound i 0 1) ++
        [and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7),
         and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7),
         and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7),
         or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7)] ++
        [at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2] ++
        [not_equals_const (6:Fin 7) 1]
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 0 1 a hb
    have h2' : a i ≤ 1 := by exact_mod_cast h2
    show a i ∈ domainValues 0 1
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  have hb0 : a (0:Fin 7) ≤ 1 := (mem_domainValues.mp (hdom (0:Fin 7))).2
  have hb1 : a (1:Fin 7) ≤ 1 := (mem_domainValues.mp (hdom (1:Fin 7))).2
  have hb2 : a (2:Fin 7) ≤ 1 := (mem_domainValues.mp (hdom (2:Fin 7))).2
  have hg1 : a (0:Fin 7) + a (1:Fin 7) - 1 ≤ a (3:Fin 7) := by
    refine and_all2_lower_sat 0 1 3 a hb0 hb1 (hsol _ ?_)
    show and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7) ∈
      (List.finRange 7).map (fun i => bound i 0 1) ++
      [and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7),
       and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7),
       and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7),
       or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7)] ++
      [at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2] ++ [not_equals_const (6:Fin 7) 1]
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_cons_self
  have hg2 : a (1:Fin 7) + a (2:Fin 7) - 1 ≤ a (4:Fin 7) := by
    refine and_all2_lower_sat 1 2 4 a hb1 hb2 (hsol _ ?_)
    show and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7) ∈
      (List.finRange 7).map (fun i => bound i 0 1) ++
      [and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7),
       and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7),
       and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7),
       or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7)] ++
      [at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2] ++ [not_equals_const (6:Fin 7) 1]
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have hg3 : a (0:Fin 7) + a (2:Fin 7) - 1 ≤ a (5:Fin 7) := by
    refine and_all2_lower_sat 0 2 5 a hb0 hb2 (hsol _ ?_)
    show and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7) ∈
      (List.finRange 7).map (fun i => bound i 0 1) ++
      [and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7),
       and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7),
       and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7),
       or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7)] ++
      [at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2] ++ [not_equals_const (6:Fin 7) 1]
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hor : a (3:Fin 7) ≤ a (6:Fin 7) ∧ a (4:Fin 7) ≤ a (6:Fin 7) ∧ a (5:Fin 7) ≤ a (6:Fin 7) := by
    refine or_all3_le_sat 3 4 5 6 a (hsol _ ?_)
    show or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7) ∈
      (List.finRange 7).map (fun i => bound i 0 1) ++
      [and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7),
       and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7),
       and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7),
       or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7)] ++
      [at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2] ++ [not_equals_const (6:Fin 7) 1]
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hatleast : a (0:Fin 7) + a (1:Fin 7) + a (2:Fin 7) ≥ 2 := by
    refine at_least3_2_sat 0 1 2 a (hsol _ ?_)
    show at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2 ∈
      (List.finRange 7).map (fun i => bound i 0 1) ++
      [and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7),
       and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7),
       and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7),
       or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7)] ++
      [at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2] ++ [not_equals_const (6:Fin 7) 1]
    apply List.mem_append_left; apply List.mem_append_right; exact List.mem_cons_self
  have hneq : a (6:Fin 7) ≠ 1 := by
    refine not_equals_const_sat (6:Fin 7) 1 a (hsol _ ?_)
    show not_equals_const (6:Fin 7) 1 ∈
      (List.finRange 7).map (fun i => bound i 0 1) ++
      [and_all (⟨#[(0:Fin 7),(1:Fin 7)], rfl⟩) (3:Fin 7),
       and_all (⟨#[(1:Fin 7),(2:Fin 7)], rfl⟩) (4:Fin 7),
       and_all (⟨#[(0:Fin 7),(2:Fin 7)], rfl⟩) (5:Fin 7),
       or_all (⟨#[(3:Fin 7),(4:Fin 7),(5:Fin 7)], rfl⟩) (6:Fin 7)] ++
      [at_least_k (⟨#[(0:Fin 7),(1:Fin 7),(2:Fin 7)], rfl⟩) 2] ++ [not_equals_const (6:Fin 7) 1]
    apply List.mem_append_right; exact List.mem_cons_self
  exact circ_no_sol ⟨a, fun _ => false, hdom, hg1, hg2, hg3, hor.1, hor.2.1, hor.2.2, hatleast, hneq⟩

end CSP.L2S.PB.Circuit
