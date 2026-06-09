import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«10_langford_simple»

namespace CSP.L2S.PB.Langford

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for Langford's problem `L(2,2)`

`langford_2n_csp 2` (`Tests/lean/10_langford_simple.lean`, CSPLib #024) places two
copies each of the digits `1, 2` into four positions `a 0..a 3 ∈ {1,2,3,4}` such
that the two copies of digit `d` are exactly `d+1` positions apart, and all four
positions differ:

* digit 1 (`a 0, a 1`): `a 1 - a 0 = 2`  (`linear_eq` spacing);
* digit 2 (`a 2, a 3`): `a 3 - a 2 = 3`  (`linear_eq` spacing);
* `alldifferent (Vector.ofFn id)` on `a 0..a 3`.

`L(2,n)` is solvable iff `n ≡ 0, 3 (mod 4)`, so `L(2,2)` is unsatisfiable:
`a 3 - a 2 = 3` forces `(a 2, a 3) = (1, 4)`, leaving `a 0, a 1 ∈ {2, 3}` distinct,
but then `a 1 - a 0 ∈ {-1, 1} ≠ 2`.

This is the **first end-to-end consumer of `linear_eq`** (via the new
`linear_eq_sat` bridge in `Adapter.lean`, which splits the equality into the two
`≤` facts the linear fragment encodes) and the **first instance mixing the linear
and `alldifferent` encoders**.  Both encoders are aux-free, so the instance rides
the generic spine `csp_unsat_generic`: each spacing equality contributes two
`encodeLinearLe` constraints and the `alldifferent` contributes the per-value
cardinality clauses (`encodeAllDifferent`).  For the domain `{1,2,3,4}` (width 3)
each position has three threshold bits, so position `i` maps to OPB `x{3i+1..3i+3}`
and the order-encoding `monotonicity` staircase is non-empty.
-/

/-! ### The signature and PB encoding -/

/-- The PB signature for `L(2,2)`: four integer (position) variables over the
    domain `{1,2,3,4}`, no Boolean or auxiliary variables (both encoders are
    aux-free). -/
def lfSig : CSPSig where
  nInt := 4
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 4
  sorted := fun _ => domainValues_sorted 1 4
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The PB user constraints: each spacing equality `Σ = target` as its two `≤`
    halves (`a 1 - a 0 ≤ 2` / `≥ 2`, `a 3 - a 2 ≤ 3` / `≥ 3`), plus the
    `alldifferent` per-value cardinality clauses over `{1,2,3,4}`.  (The `a 3 - a 2 ≤ 3`
    half normalizes away as a tautology — the domain max gap is `3` — leaving five
    user clauses; the order-encoding staircase is added by the spine.) -/
def lfUser : List (PBConstr (PBVar lfSig)) :=
  (normalize (encodeLinearLe [(1, (1 : Fin 4)), (-1, (0 : Fin 4))] 2)).toList ++
  (normalize (encodeLinearLe [(1, (0 : Fin 4)), (-1, (1 : Fin 4))] (-2))).toList ++
  (normalize (encodeLinearLe [(1, (3 : Fin 4)), (-1, (2 : Fin 4))] 3)).toList ++
  (normalize (encodeLinearLe [(1, (2 : Fin 4)), (-1, (3 : Fin 4))] (-3))).toList ++
  (encodeAllDifferent [(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)] [1, 2, 3, 4]).filterMap
    normalize

/-! ### The PB certificate -/

/-- The veripb-elaborated kernel proof of UNSAT for `lfUser`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  Position `i` maps to OPB thresholds
    `x{3i+1..3i+3}` (12 variables). -/
def lfKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 15;
rup >= 0 : ~ ;
rup 1 x7 >= 1 : ~ 11;
rup 1 x8 >= 1 : ~ 11;
rup 1 x9 >= 1 : ~ 11;
rup 1 ~x10 >= 1 : ~ 11;
rup 1 ~x11 >= 1 : ~ 11;
rup 1 ~x12 >= 1 : ~ 11;
rup 1 x7 1 x10 >= 1 : ~ 17;
pol 12 23 +;
rup 1 ~x1 >= 1 : ~ 24;
rup 1 ~x4 >= 1 : ~ 24;
rup 1 x2 >= 1 : ~ 25 10;
rup 1 x3 >= 1 : ~ 25 10;
rup 1 ~x5 >= 1 : ~ 25 10;
rup 1 ~x6 >= 1 : ~ 25 10;
rup 1 ~x3 1 ~x6 1 ~x9 1 ~x12 >= 2 : 30 22 ~;
pol 15 31 +;
output NONE ;
conclusion UNSAT : 32;
end pseudo-Boolean proof;
"

/-- The PB encoding of `L(2,2)` is unsatisfiable — established by the external PB
    certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are
    untrusted). -/
theorem lf_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((lfSig.monotonicity ++ lfUser).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 12 lfKernelProof (by native_decide)

/-! ### The end-to-end theorem -/

/-- The generic spine rules out any in-domain placement satisfying both spacing
    equalities and the all-different requirement. -/
theorem lf_no_sol : ¬ ∃ (a : Fin lfSig.nInt → Int) (_ : Fin lfSig.nBool → Bool),
    (∀ i, a i ∈ lfSig.values i) ∧
    (a (1 : Fin 4) - a (0 : Fin 4) = 2 ∧
     a (3 : Fin 4) - a (2 : Fin 4) = 3 ∧
     ([(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)].map a).Nodup) := by
  apply csp_unsat_generic lfSig lfUser
    (fun a _ => a (1 : Fin 4) - a (0 : Fin 4) = 2 ∧ a (3 : Fin 4) - a (2 : Fin 4) = 3 ∧
      ([(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)].map a).Nodup)
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    obtain ⟨hE1, hE2, hND⟩ := hP
    unfold lfUser at hc
    rw [List.mem_append, List.mem_append, List.mem_append, List.mem_append] at hc
    rcases hc with (((hc | hc) | hc) | hc) | hc
    · -- a 1 - a 0 ≤ 2
      rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (1 : Fin 4)), (-1, (0 : Fin 4))] 2 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · -- a 0 - a 1 ≤ -2   (i.e. a 1 - a 0 ≥ 2)
      rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (0 : Fin 4)), (-1, (1 : Fin 4))] (-2) c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · -- a 3 - a 2 ≤ 3
      rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (3 : Fin 4)), (-1, (2 : Fin 4))] 3 c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · -- a 2 - a 3 ≤ -3   (i.e. a 3 - a 2 ≥ 3)
      rw [Option.mem_toList] at hc
      refine extend_sat_encodeLinearLe a bA _ hdom [(1, (2 : Fin 4)), (-1, (3 : Fin 4))] (-3) c hc ?_
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
    · -- alldifferent over the four positions
      exact extend_sat_encodeAllDifferent a bA _ hdom
        [(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)] [1, 2, 3, 4] c hc hND
  · exact lf_formulaUnsat

/-- **End-to-end Langford UNSAT.** The corpus CSP `langford_2n_csp 2` — Langford's
    problem `L(2,2)` — is unsatisfiable, discharged through the verified PB
    pipeline: the `linear_eq` spacing bridge and the `alldifferent` bridge turn any
    solution into the two equalities and the all-different fact, the generic spine
    `csp_unsat_generic` turns those into a PB model (linear `≤` halves +
    cardinality clauses), and the committed certificate `lf_formulaUnsat`
    contradicts it. -/
theorem langford_2_2_unsat : ¬ (langford_2n_csp 2).isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Every position lies in `{1,2,3,4}` (from its `bound`).
  have hdom : ∀ i : Fin lfSig.nInt, a i ∈ lfSig.values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 1 (4 : ℕ)) a := by
      apply hsol
      apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
    obtain ⟨h1, h2⟩ := bound_sat i 1 (4 : ℕ) a hb
    have h2' : a i ≤ 4 := by exact_mod_cast h2
    show a i ∈ domainValues 1 4
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- The two spacing equalities (from the `linear_eq` constraints).
  have hE1 : a (1 : Fin 4) - a (0 : Fin 4) = 2 := by
    have hs : IntCSP.satisfiesConstraintInt
        (make_spacing_constraint 4 0 1 1 (by decide) (by decide)) a := by
      apply hsol
      apply List.mem_append_left; apply List.mem_append_right
      show make_spacing_constraint 4 0 1 1 (by decide) (by decide) ∈
        [make_spacing_constraint 4 0 1 1 (by decide) (by decide),
         make_spacing_constraint 4 2 3 2 (by decide) (by decide)]
      exact List.mem_cons_self
    have hsum := linear_eq_sat (⟨#[⟨1, by decide⟩, ⟨0, by decide⟩], rfl⟩ : _root_.Vector (Fin 4) 2)
      ⟨#[1, -1], rfl⟩ 2 a hs
    simp at hsum
    linarith [hsum]
  have hE2 : a (3 : Fin 4) - a (2 : Fin 4) = 3 := by
    have hs : IntCSP.satisfiesConstraintInt
        (make_spacing_constraint 4 2 3 2 (by decide) (by decide)) a := by
      apply hsol
      apply List.mem_append_left; apply List.mem_append_right
      show make_spacing_constraint 4 2 3 2 (by decide) (by decide) ∈
        [make_spacing_constraint 4 0 1 1 (by decide) (by decide),
         make_spacing_constraint 4 2 3 2 (by decide) (by decide)]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    have hsum := linear_eq_sat (⟨#[⟨3, by decide⟩, ⟨2, by decide⟩], rfl⟩ : _root_.Vector (Fin 4) 2)
      ⟨#[1, -1], rfl⟩ 3 a hs
    simp at hsum
    linarith [hsum]
  -- The positions are all different (from the `alldifferent` constraint).
  have hND : ([(0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4)].map a).Nodup := by
    have h := alldifferent_sat (_root_.Vector.ofFn id) a (by
      apply hsol
      apply List.mem_append_right
      exact List.mem_cons_self)
    -- `(Vector.ofFn id).toList` is defeq to the literal position list.
    exact h
  exact lf_no_sol ⟨a, fun _ => false, hdom, hE1, hE2, hND⟩

end CSP.L2S.PB.Langford
