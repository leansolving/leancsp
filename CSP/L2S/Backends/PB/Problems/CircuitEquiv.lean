import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«31_circuit_equivalence»

namespace CSP.L2S.PB.CircuitEquiv

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for a circuit-*equivalence* corpus CSP

This is the **first XOR circuit** and the **first equivalence-checking** consumer of
the PB pipeline.  The corpus CSP `xor_equivalence`
(`Tests/lean/31_circuit_equivalence.lean`) asks whether two implementations of
2-input XOR ever disagree:

* circuit 1 — a single XOR gate `out₁ = a ⊕ b` (node 2);
* circuit 2 — the textbook decomposition `out₂ = (a ∧ ¬b) ∨ (¬a ∧ b)` (node 7),
  built from `NOT`, `AND`, `OR` gates (nodes 3–7);

with the *negated* equivalence `out₁ ≠ out₂`.  It is **unsatisfiable** — the two
circuits are equivalent — which is exactly the miter-based equivalence-checking
property.

The key observation that keeps this in the **linear** PB fragment (no Tseitin /
`BoolExpr` machinery, no aux variables) is that *2-input* gates over `{0,1}` each
have an **exact** integer-linear characterisation:

* `r = AND(x,y)` (`= min`)  ⟺  `r ≤ x`, `r ≤ y`, `x + y - 1 ≤ r`;
* `r = OR(x,y)`  (`= max`)  ⟺  `x ≤ r`, `y ≤ r`, `r ≤ x + y`;
* `r = NOT(x)`              ⟺  `r = 1 - x`;
* `r = XOR(x,y)` (`= (x+y) mod 2`)  ⟺  `r ≤ x+y`, `x-y ≤ r`, `y-x ≤ r`, `r ≤ 2-x-y`;
* `out₁ ≠ out₂` over `{0,1}`  ⟺  `out₁ + out₂ = 1`.

(Only `xor_all`/`and_all` of arity `≥ 3` — genuine parity / many-input fan-in — is
non-linear and would need the `BoolExpr` compiler; the corpus circuit here is built
entirely from arity-2 gates.)  All of these consequences are linear / equalities, so
the proof rides the existing `encodeLinearLe` encoder through the generic aux-free
spine `csp_unsat_generic`.

The builder `xor_equivalence` reduces definitionally to its explicit constraint
list, so corpus-constraint membership is direct (no `filterMap`/`foldl` navigation).
-/

/-! ### Pure-`ℤ` helper lemmas

`omega` does not unfold the `IntDomain := ℤ` abbreviation, so it cannot
reason about `a i` (an `omega`-opaque atom) on the corpus side — in particular it
cannot discharge the `% 2` of the XOR checker or the `≠`→sum step.  We isolate those
two facts as pure-`ℤ` lemmas (where `omega` is at home) and apply them to the
`IntDomain` values, which are *defeq* to `ℤ`. -/

/-- The exact linear characterisation of 2-input XOR over `{0,1}`: from
    `(X + Y) mod 2 = R` and `X, Y ∈ {0,1}`, the four linear bounds follow (the value
    of `R` — hence its `{0,1}` membership — is pinned by the `% 2` hypothesis). -/
theorem xor_facts_int (X Y R : ℤ) (hx0 : 0 ≤ X) (hx1 : X ≤ 1) (hy0 : 0 ≤ Y) (hy1 : Y ≤ 1)
    (h : (X + Y) % 2 = R) :
    R ≤ X + Y ∧ X - Y ≤ R ∧ Y - X ≤ R ∧ R ≤ 2 - X - Y := by omega

/-- Two `{0,1}` values that differ must sum to `1`. -/
theorem ne_sum_one_int (X Y : ℤ) (hx0 : 0 ≤ X) (hx1 : X ≤ 1) (hy0 : 0 ≤ Y) (hy1 : Y ≤ 1)
    (h : X ≠ Y) : X + Y = 1 := by omega

/-! ### Corpus gate bridges: each gate becomes its exact linear facts

These mirror the s11 majority-circuit bridges (`and_all2_lower_sat` etc.) but give
the **full both-directional** characterisation needed for equivalence checking (a
one-sided relaxation would leave the miter spuriously satisfiable).  They are stated
generically over the variable count `n`. -/

/-- **Bridge.** A satisfied 2-input `xor_all [x,y] r` over `{0,1}` (`r = (x+y) mod 2`)
    gives the four exact XOR bounds.  Reduces the `getLast?`/`dropLast`/`sum % 2`
    checker, then applies `xor_facts_int` to the `{0,1}` values. -/
theorem xor_all2_full_sat {n : ℕ} (x y r : Fin n) (a : IntAssignment n)
    (hx0 : 0 ≤ a x) (hx1 : a x ≤ 1) (hy0 : 0 ≤ a y) (hy1 : a y ≤ 1)
    (h : IntCSP.satisfiesConstraintInt
      (xor_all (⟨#[x, y], rfl⟩ : _root_.Vector (VarType n) 2) r) a) :
    a r ≤ a x + a y ∧ a x - a y ≤ a r ∧ a y - a x ≤ a r ∧ a r ≤ 2 - a x - a y := by
  simp only [IntCSP.satisfiesConstraintInt, xor_all, patternHolds, map_valAt, valAt_eq] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at h
  exact xor_facts_int (a x) (a y) (a r) hx0 hx1 hy0 hy1 h

/-- **Bridge.** A satisfied `not_gate i o` gives `a o = 1 - a i` (the exact NOT
    relation; the checker `decide (z = 1 - x)` reduces directly). -/
theorem not_gate_eq_sat {n : ℕ} (i o : Fin n) (a : IntAssignment n)
    (h : IntCSP.satisfiesConstraintInt (not_gate i o) a) :
    a o = 1 - a i := by
  simp only [IntCSP.satisfiesConstraintInt, not_gate, patternHolds, valAt_eq] at h
  exact h

/-- **Bridge.** A satisfied 2-input `and_all [x,y] r` over `{0,1}` (`r = min(x,y)`)
    gives the three exact AND bounds (the lower bound `x + y - 1 ≤ r` uses the upper
    domain bounds).  The `foldl`-min checker is reduced then `split_ifs` + `linarith`. -/
theorem and_all2_full_sat {n : ℕ} (x y r : Fin n) (a : IntAssignment n)
    (hx : a x ≤ 1) (hy : a y ≤ 1)
    (h : IntCSP.satisfiesConstraintInt
      (and_all (⟨#[x, y], rfl⟩ : _root_.Vector (VarType n) 2) r) a) :
    a r ≤ a x ∧ a r ≤ a y ∧ a x + a y - 1 ≤ a r := by
  simp only [IntCSP.satisfiesConstraintInt, and_all, patternHolds, map_valAt, valAt_eq] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.headI,
    List.foldl_cons, List.foldl_nil, ne_eq] at h
  obtain ⟨-, h⟩ := h
  split_ifs at h <;> exact ⟨by linarith, by linarith, by linarith⟩

/-- **Bridge.** A satisfied 2-input `or_all [x,y] r` over `{0,1}` (`r = max(x,y)`)
    gives the three exact OR bounds (the upper bound `r ≤ x + y` uses the lower
    domain bounds).  The `foldl`-max checker is reduced then `split_ifs` + `linarith`. -/
theorem or_all2_full_sat {n : ℕ} (x y r : Fin n) (a : IntAssignment n)
    (hx : 0 ≤ a x) (hy : 0 ≤ a y)
    (h : IntCSP.satisfiesConstraintInt
      (or_all (⟨#[x, y], rfl⟩ : _root_.Vector (VarType n) 2) r) a) :
    a x ≤ a r ∧ a y ≤ a r ∧ a r ≤ a x + a y := by
  simp only [IntCSP.satisfiesConstraintInt, or_all, patternHolds, map_valAt, valAt_eq] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.headI,
    List.foldl_cons, List.foldl_nil, ne_eq] at h
  obtain ⟨-, h⟩ := h
  split_ifs at h <;> exact ⟨by linarith, by linarith, by linarith⟩

/-! ### The signature and PB encoding -/

/-- The PB signature: eight Boolean nodes (`a, b`, the XOR output, the two `NOT`s,
    the two `AND`s, and the `OR` output), each over the domain `{0,1}`, no Booleans
    or auxiliaries. -/
def xorSig : CSPSig where
  nInt := 8
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The PB user constraints: the exact linear characterisations of all six gates
    (XOR node 2, `NOT` nodes 3/4, `AND` nodes 5/6, `OR` node 7) and the
    disequality `node₂ + node₇ = 1` of the negated equivalence.  All aux-free.

    Node `i` (domain `{0,1}`, width 1) has the single threshold `a i ≤ 0`, mapping to
    OPB variable `x{i+1}` (so `x{i+1} = ⟦node i = 0⟧`). -/
def xorUser : List (PBConstr (PBVar xorSig)) :=
  -- XOR node 2 = node 0 ⊕ node 1
  (normalize (encodeLinearLe [(1, (2:Fin 8)), (-1, (0:Fin 8)), (-1, (1:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (0:Fin 8)), (-1, (1:Fin 8)), (-1, (2:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(-1, (0:Fin 8)), (1, (1:Fin 8)), (-1, (2:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (2:Fin 8)), (1, (0:Fin 8)), (1, (1:Fin 8))] 2)).toList ++
  -- NOT node 3 = 1 - node 0
  (normalize (encodeLinearLe [(1, (0:Fin 8)), (1, (3:Fin 8))] 1)).toList ++
  (normalize (encodeLinearLe [(-1, (0:Fin 8)), (-1, (3:Fin 8))] (-1))).toList ++
  -- NOT node 4 = 1 - node 1
  (normalize (encodeLinearLe [(1, (1:Fin 8)), (1, (4:Fin 8))] 1)).toList ++
  (normalize (encodeLinearLe [(-1, (1:Fin 8)), (-1, (4:Fin 8))] (-1))).toList ++
  -- AND node 5 = min(node 0, node 4)
  (normalize (encodeLinearLe [(1, (5:Fin 8)), (-1, (0:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (5:Fin 8)), (-1, (4:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (0:Fin 8)), (1, (4:Fin 8)), (-1, (5:Fin 8))] 1)).toList ++
  -- AND node 6 = min(node 3, node 1)
  (normalize (encodeLinearLe [(1, (6:Fin 8)), (-1, (3:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (6:Fin 8)), (-1, (1:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (3:Fin 8)), (1, (1:Fin 8)), (-1, (6:Fin 8))] 1)).toList ++
  -- OR node 7 = max(node 5, node 6)
  (normalize (encodeLinearLe [(1, (5:Fin 8)), (-1, (7:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (6:Fin 8)), (-1, (7:Fin 8))] 0)).toList ++
  (normalize (encodeLinearLe [(1, (7:Fin 8)), (-1, (5:Fin 8)), (-1, (6:Fin 8))] 0)).toList ++
  -- node 2 ≠ node 7  →  node 2 + node 7 = 1
  (normalize (encodeLinearLe [(1, (2:Fin 8)), (1, (7:Fin 8))] 1)).toList ++
  (normalize (encodeLinearLe [(-1, (2:Fin 8)), (-1, (7:Fin 8))] (-1))).toList

/-- The veripb-elaborated kernel proof of UNSAT for `xorUser`'s OPB serialisation
    (RoundingSat + veripb; both untrusted).  The eight thresholds `node i ≤ 0` map to
    OPB `x1..x8`. -/
def xorKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 19;
rup >= 0 : ~ ;
pol 17 19 + 10 + 4 + 7 + s;
pol 15 11 + 18 + 8 + 2 + s 21 + s 12 + 5 + s;
rup 1 x6 >= 1 : ~ 22 9;
rup 1 ~x4 >= 1 : ~ 22 6;
pol 19 17 + 23 + 1 + 22 + 13 + s;
rup 1 ~x3 >= 1 : ~ 25 22 3;
rup 1 x5 >= 1 : ~ 25 7;
rup 1 ~x7 >= 1 : ~ 25 24 14;
rup 1 x8 >= 1 : ~ 26 18;
rup 1 ~x7 1 x8 >= 2 : 28 29 ~;
pol 16 30 +;
output NONE ;
conclusion UNSAT : 31;
end pseudo-Boolean proof;
"

/-- The PB encoding of the XOR-equivalence miter is unsatisfiable — established by the
    external PB certificate, kernel-checked through PBLean's verified reflection
    checker (`native_decide` runs the checker; RoundingSat / veripb / the serializer
    are untrusted). -/
theorem xor_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((xorSig.monotonicity ++ xorUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 8 xorKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain Boolean assignment satisfying the exact
    linear gate facts together with the disequality of the negated equivalence. -/
theorem xor_no_sol : ¬ ∃ (a : Fin xorSig.nInt → Int) (_ : Fin xorSig.nBool → Bool),
    (∀ i, a i ∈ xorSig.values i) ∧
    ((a (2:Fin 8) ≤ a (0:Fin 8) + a (1:Fin 8)) ∧
     (a (0:Fin 8) - a (1:Fin 8) ≤ a (2:Fin 8)) ∧
     (a (1:Fin 8) - a (0:Fin 8) ≤ a (2:Fin 8)) ∧
     (a (2:Fin 8) ≤ 2 - a (0:Fin 8) - a (1:Fin 8)) ∧
     (a (3:Fin 8) = 1 - a (0:Fin 8)) ∧ (a (4:Fin 8) = 1 - a (1:Fin 8)) ∧
     (a (5:Fin 8) ≤ a (0:Fin 8)) ∧ (a (5:Fin 8) ≤ a (4:Fin 8)) ∧
     (a (0:Fin 8) + a (4:Fin 8) - 1 ≤ a (5:Fin 8)) ∧
     (a (6:Fin 8) ≤ a (3:Fin 8)) ∧ (a (6:Fin 8) ≤ a (1:Fin 8)) ∧
     (a (3:Fin 8) + a (1:Fin 8) - 1 ≤ a (6:Fin 8)) ∧
     (a (5:Fin 8) ≤ a (7:Fin 8)) ∧ (a (6:Fin 8) ≤ a (7:Fin 8)) ∧
     (a (7:Fin 8) ≤ a (5:Fin 8) + a (6:Fin 8)) ∧
     (a (2:Fin 8) + a (7:Fin 8) = 1)) := by
  apply csp_unsat_generic xorSig xorUser
    (fun a _ => (a (2:Fin 8) ≤ a (0:Fin 8) + a (1:Fin 8)) ∧
     (a (0:Fin 8) - a (1:Fin 8) ≤ a (2:Fin 8)) ∧
     (a (1:Fin 8) - a (0:Fin 8) ≤ a (2:Fin 8)) ∧
     (a (2:Fin 8) ≤ 2 - a (0:Fin 8) - a (1:Fin 8)) ∧
     (a (3:Fin 8) = 1 - a (0:Fin 8)) ∧ (a (4:Fin 8) = 1 - a (1:Fin 8)) ∧
     (a (5:Fin 8) ≤ a (0:Fin 8)) ∧ (a (5:Fin 8) ≤ a (4:Fin 8)) ∧
     (a (0:Fin 8) + a (4:Fin 8) - 1 ≤ a (5:Fin 8)) ∧
     (a (6:Fin 8) ≤ a (3:Fin 8)) ∧ (a (6:Fin 8) ≤ a (1:Fin 8)) ∧
     (a (3:Fin 8) + a (1:Fin 8) - 1 ≤ a (6:Fin 8)) ∧
     (a (5:Fin 8) ≤ a (7:Fin 8)) ∧ (a (6:Fin 8) ≤ a (7:Fin 8)) ∧
     (a (7:Fin 8) ≤ a (5:Fin 8) + a (6:Fin 8)) ∧
     (a (2:Fin 8) + a (7:Fin 8) = 1))
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hP
    simp only [xorUser, List.mem_append] at hc
    rcases hc with (((((((((((((((((hc | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) |
      hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc) | hc
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (2:Fin 8)), (-1, (0:Fin 8)), (-1, (1:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (0:Fin 8)), (-1, (1:Fin 8)), (-1, (2:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(-1, (0:Fin 8)), (1, (1:Fin 8)), (-1, (2:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (2:Fin 8)), (1, (0:Fin 8)), (1, (1:Fin 8))] 2 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (0:Fin 8)), (1, (3:Fin 8))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(-1, (0:Fin 8)), (-1, (3:Fin 8))] (-1) c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (1:Fin 8)), (1, (4:Fin 8))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(-1, (1:Fin 8)), (-1, (4:Fin 8))] (-1) c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (5:Fin 8)), (-1, (0:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (5:Fin 8)), (-1, (4:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (0:Fin 8)), (1, (4:Fin 8)), (-1, (5:Fin 8))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (6:Fin 8)), (-1, (3:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (6:Fin 8)), (-1, (1:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (3:Fin 8)), (1, (1:Fin 8)), (-1, (6:Fin 8))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (5:Fin 8)), (-1, (7:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (6:Fin 8)), (-1, (7:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom
        [(1, (7:Fin 8)), (-1, (5:Fin 8)), (-1, (6:Fin 8))] 0 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (2:Fin 8)), (1, (7:Fin 8))] 1 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(-1, (2:Fin 8)), (-1, (7:Fin 8))] (-1) c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
  · exact xor_formulaUnsat

/-- **End-to-end circuit-equivalence UNSAT.** The corpus CSP `xor_equivalence`
    (`Tests/lean/31_circuit_equivalence.lean`) — do the direct XOR gate and the
    `(a ∧ ¬b) ∨ (¬a ∧ b)` decomposition ever disagree? — is unsatisfiable, i.e. the
    two circuits are equivalent.  Discharged through the verified PB pipeline: the
    exact gate bridges (XOR, AND, OR, NOT) and the `≠`→sum bridge turn any
    counterexample into sixteen linear / equality facts, the generic spine
    `csp_unsat_generic` turns those into a PB model via the aux-free `encodeLinearLe`
    encoder, and the committed certificate `xor_formulaUnsat` contradicts it.
    No Tseitin / `BoolExpr` machinery — every arity-2 gate is exactly linear
    over `{0,1}`. -/
theorem xor_equivalence_unsat : ¬ xor_equivalence.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Reduce the corpus solution to one over the explicit constraint list (defeq).
  have hsol' : ∀ c ∈ ((List.finRange 8).map (fun i => bound i 0 1) ++
      [xor_all (⟨#[(0:Fin 8), (1:Fin 8)], rfl⟩) (2:Fin 8)] ++
      [not_gate (0:Fin 8) (3:Fin 8), not_gate (1:Fin 8) (4:Fin 8),
       and_all (⟨#[(0:Fin 8), (4:Fin 8)], rfl⟩) (5:Fin 8),
       and_all (⟨#[(3:Fin 8), (1:Fin 8)], rfl⟩) (6:Fin 8),
       or_all (⟨#[(5:Fin 8), (6:Fin 8)], rfl⟩) (7:Fin 8)] ++
      [not_equal (2:Fin 8) (7:Fin 8)]),
      IntCSP.satisfiesConstraintInt c a := hsol
  -- Every node lies in the Boolean domain {0,1}.
  have hdom : ∀ i : Fin xorSig.nInt, a i ∈ xorSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 0 1) a :=
      hsol' (bound i 0 1)
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩))))
    obtain ⟨h1, h2⟩ := bound_sat i 0 1 a hb
    show a i ∈ domainValues 0 1
    exact mem_domainValues.mpr ⟨h1, h2⟩
  have hbd : ∀ i : Fin 8, 0 ≤ a i ∧ a i ≤ 1 := fun i => mem_domainValues.mp (hdom i)
  -- Gate facts via the exact bridges.
  have hxor := xor_all2_full_sat (0:Fin 8) (1:Fin 8) (2:Fin 8) a
    (hbd 0).1 (hbd 0).2 (hbd 1).1 (hbd 1).2
    (hsol' _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      List.mem_cons_self))))
  have hnot3 : a (3:Fin 8) = 1 - a (0:Fin 8) := not_gate_eq_sat (0:Fin 8) (3:Fin 8) a
    (hsol' _ (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)))
  have hnot4 : a (4:Fin 8) = 1 - a (1:Fin 8) := not_gate_eq_sat (1:Fin 8) (4:Fin 8) a
    (hsol' _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ List.mem_cons_self))))
  have hand5 := and_all2_full_sat (0:Fin 8) (4:Fin 8) (5:Fin 8) a (hbd 0).2 (hbd 4).2
    (hsol' _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  have hand6 := and_all2_full_sat (3:Fin 8) (1:Fin 8) (6:Fin 8) a (hbd 3).2 (hbd 1).2
    (hsol' _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self))))))
  have hor7 := or_all2_full_sat (5:Fin 8) (6:Fin 8) (7:Fin 8) a (hbd 5).1 (hbd 6).1
    (hsol' _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)))))))
  have hne : a (2:Fin 8) ≠ a (7:Fin 8) := not_equal_sat (2:Fin 8) (7:Fin 8) a
    (hsol' _ (List.mem_append_right _ List.mem_cons_self))
  have hdiseq : a (2:Fin 8) + a (7:Fin 8) = 1 :=
    ne_sum_one_int (a (2:Fin 8)) (a (7:Fin 8)) (hbd 2).1 (hbd 2).2 (hbd 7).1 (hbd 7).2 hne
  exact xor_no_sol ⟨a, fun _ => false, hdom,
    hxor.1, hxor.2.1, hxor.2.2.1, hxor.2.2.2, hnot3, hnot4,
    hand5.1, hand5.2.1, hand5.2.2, hand6.1, hand6.2.1, hand6.2.2,
    hor7.1, hor7.2.1, hor7.2.2, hdiseq⟩

end CSP.L2S.PB.CircuitEquiv
