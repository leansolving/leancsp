import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«02_color»

namespace CSP.L2S.PB.OddCycle

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for odd-cycle 2-colourability (`c5/c7/c9_2col`)

The odd cycle `C_n` on vertices `0..n-1` (edges `(i, i+1)`, closing `(n-1, 0)`) is
not 2-colourable for odd `n`.  These theorems **scale** `k3_2col` (`C_3`, the
triangle, in `GraphColoring.lean`): the same binary `not_equal`-per-edge encoding,
just on a longer cycle.  They are the *easy non-separation baseline* of the scaling
study (`docs/SCALING.md`): every coefficient is `0/1`, so both the verified
cutting-planes certificate and a resolution (DRAT) proof grow only linearly — the
control that isolates the pigeonhole / mutilated-chessboard walls as
resolution-specific.

The proof is **generic in the cycle**.  `cycle_2col_unsat n edges hunsat` discharges
`¬ (graph_coloring_csp n edges 2).isSatisfiableInt` from a single committed PB
certificate (`hunsat`), exactly as `k3_2col_unsat` does, via the binary
not-all-equal bridge (`not_equal_sat` / `extend_sat_encodeNotAllEqualBin`) and the
generic spine `csp_unsat_generic`.  Each concrete cycle then supplies only its
RoundingSat+veripb certificate.

For the binary colour domain `{1,2}` each vertex has a single threshold bit, so the
order-encoding `monotonicity` is empty and vertex `i` maps to OPB `x{i+1}`; each edge
`(u,v)` becomes the two clauses `x_u + x_v ≥ 1` and `¬x_u + ¬x_v ≥ 1`.
-/

/-! ### Generic cycle infrastructure -/

/-- The PB signature for an `n`-vertex 2-colouring: `n` integer (colour) variables,
    each over the binary domain `{1,2}`, no Boolean or auxiliary variables. -/
def cycleSig (n : ℕ) : CSPSig where
  nInt := n
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 2
  sorted := fun _ => domainValues_sorted 1 2
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- Every colour variable has the single-threshold (binary) domain, width `1 > 0`. -/
theorem cycleSig_width (n : ℕ) (i : Fin (cycleSig n).nInt) : 0 < (cycleSig n).width i := by
  show 0 < (domainValues 1 2).length - 1; decide

/-- Each edge's `not_equal` constraint is in the colouring CSP's constraint list (it is
    one of the `edge_constraints`, the right summand of the list). -/
theorem cycle_edge_mem (n : ℕ) (edges : List (Fin n × Fin n))
    (e : Fin n × Fin n) (he : e ∈ edges) :
    not_equal e.1 e.2 ∈ (graph_coloring_csp n edges 2).constraints := by
  obtain ⟨u, v⟩ := e
  show not_equal u v ∈ bound_constraints n 2 ++ edge_constraints n edges
  apply List.mem_append_right
  rw [edge_constraints, List.mem_map]
  exact ⟨(u, v), he, rfl⟩

/-- The PB user constraints: per edge, the normalized binary not-all-equal encoding of
    its two endpoints (the order-encoding staircase clauses are added by the spine and
    are empty here, since every domain is binary). -/
def cycleUser (n : ℕ) (edges : List (Fin n × Fin n)) :
    List (PBConstr (PBVar (cycleSig n))) :=
  edges.flatMap (fun e =>
    (encodeNotAllEqualBin [e.1, e.2] (fun i _ => cycleSig_width n i)).filterMap normalize)

/-- The generic spine rules out any in-domain 2-colouring under which every edge is
    bichromatic — given a committed PB certificate for the encoding. -/
theorem cycle_no_sol (n : ℕ) (edges : List (Fin n × Fin n))
    (hunsat : VeriPB.Reflect.formulaUnsat
      (((cycleSig n).monotonicity ++ cycleUser n edges).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ (a : Fin (cycleSig n).nInt → Int) (_ : Fin (cycleSig n).nBool → Bool),
      (∀ i, a i ∈ (cycleSig n).values i) ∧ (∀ e ∈ edges, a e.1 ≠ a e.2) := by
  apply csp_unsat_generic (cycleSig n) (cycleUser n edges)
    (fun a _ => ∀ e ∈ edges, a e.1 ≠ a e.2)
    (fun _ _ _ => false)
  · intro a bA hdom hP c hc
    simp only [cycleUser, List.mem_flatMap] at hc
    obtain ⟨e, he, hc⟩ := hc
    refine extend_sat_encodeNotAllEqualBin a bA _ hdom [e.1, e.2]
      (fun i _ => cycleSig_width n i) 1 2
      (fun i _ => by show domainValues 1 2 = [(1 : Int), 2]; decide) ?_ c hc
    exact ⟨e.1, by simp, e.2, by simp, hP e he⟩
  · exact hunsat

/-- **Generic odd-cycle 2-colouring UNSAT.** Given a committed PB certificate for the
    encoding, the colouring CSP `graph_coloring_csp n edges 2` is unsatisfiable.  The
    `not_equal` bridge turns any solution into a "differ" fact on each edge, the generic
    spine `csp_unsat_generic` turns those into a PB model, and the certificate
    contradicts it.  For an odd cycle the premise is genuinely unsatisfiable, so each
    `c?_2col_unsat` below is a faithful "C_n is not 2-colourable" theorem. -/
theorem cycle_2col_unsat (n : ℕ) (edges : List (Fin n × Fin n))
    (hunsat : VeriPB.Reflect.formulaUnsat
      (((cycleSig n).monotonicity ++ cycleUser n edges).toArray.map PBConstr.toNatConstr)) :
    ¬ (graph_coloring_csp n edges 2).isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  -- Every colour lies in `{1,2}` (from its `bound`).
  have hdom : ∀ i : Fin (cycleSig n).nInt, a i ∈ (cycleSig n).values i := by
    intro i
    have hb : IntCSP.satisfiesConstraintInt (bound i 1 (2 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (2 : ℕ) a hb
    have h2' : a i ≤ 2 := by exact_mod_cast h2
    show a i ∈ domainValues 1 2
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- Every edge is bichromatic (from its `not_equal`).
  have hP : ∀ e ∈ edges, a e.1 ≠ a e.2 := by
    intro e he
    exact not_equal_sat e.1 e.2 a (hsol _ (cycle_edge_mem n edges e he))
  exact cycle_no_sol n edges hunsat ⟨a, fun _ => false, hdom, hP⟩

/-! ### `C_5` — the pentagon -/

/-- The veripb-elaborated kernel proof of UNSAT for `C_5`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  Vertex `i` maps to OPB `x{i+1}`; the ten
    clauses are `x_u + x_v ≥ 1` / `¬x_u + ¬x_v ≥ 1` per edge. -/
def c5KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 10;
rup >= 0 : ~ ;
pol 5 8 + 4 + 9 + 1 + s;
rup 1 ~x2 >= 1 : ~ 12 2;
rup 1 ~x5 >= 1 : ~ 12 10;
rup 1 x3 >= 1 : ~ 13 3;
rup 1 x4 >= 1 : ~ 14 7;
rup 1 x3 1 x4 >= 2 : 15 16 ~;
pol 6 17 +;
output NONE ;
conclusion UNSAT : 18;
end pseudo-Boolean proof;
"

/-- The PB encoding of `C_5` 2-colouring is unsatisfiable — kernel-checked through
    PBLean's verified reflection checker (`native_decide` runs the checker; RoundingSat /
    veripb / the serializer are untrusted). -/
theorem c5_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      (((cycleSig 5).monotonicity ++ cycleUser 5 c5Edges).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 5 c5KernelProof (by native_decide)

/-- **The odd cycle `C_5` is not 2-colourable.** The corpus CSP `c5_2col` — colour the
    pentagon with two colours — is unsatisfiable, discharged through the verified PB
    pipeline by the generic `cycle_2col_unsat` and the committed certificate. -/
theorem c5_2col_unsat : ¬ c5_2col.isSatisfiableInt :=
  cycle_2col_unsat 5 c5Edges c5_formulaUnsat

/-! ### `C_7` -/

/-- The veripb-elaborated kernel proof of UNSAT for `C_7`'s OPB serialization. -/
def c7KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 14;
rup >= 0 : ~ ;
pol 8 9 + 5 + 12 + 4 + 13 + 1 + s;
rup 1 ~x2 >= 1 : ~ 16 2;
rup 1 ~x7 >= 1 : ~ 16 14;
rup 1 x3 >= 1 : ~ 17 3;
rup 1 x6 >= 1 : ~ 18 11;
rup 1 ~x4 >= 1 : ~ 19 6;
rup 1 ~x5 >= 1 : ~ 20 10;
rup 1 ~x4 1 ~x5 >= 2 : 21 22 ~;
pol 7 23 +;
output NONE ;
conclusion UNSAT : 24;
end pseudo-Boolean proof;
"

/-- The PB encoding of `C_7` 2-colouring is unsatisfiable — kernel-checked. -/
theorem c7_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      (((cycleSig 7).monotonicity ++ cycleUser 7 c7Edges).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 7 c7KernelProof (by native_decide)

/-- **The odd cycle `C_7` is not 2-colourable.** -/
theorem c7_2col_unsat : ¬ c7_2col.isSatisfiableInt :=
  cycle_2col_unsat 7 c7Edges c7_formulaUnsat

/-! ### `C_9` -/

/-- The veripb-elaborated kernel proof of UNSAT for `C_9`'s OPB serialization. -/
def c9KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 18;
rup >= 0 : ~ ;
pol 9 12 + 8 + 13 + 5 + 16 + 4 + 17 + 1 + s;
rup 1 ~x2 >= 1 : ~ 20 2;
rup 1 ~x9 >= 1 : ~ 20 18;
rup 1 x3 >= 1 : ~ 21 3;
rup 1 x8 >= 1 : ~ 22 15;
rup 1 ~x4 >= 1 : ~ 23 6;
rup 1 ~x7 >= 1 : ~ 24 14;
rup 1 x5 >= 1 : ~ 25 7;
rup 1 x6 >= 1 : ~ 26 11;
rup 1 x5 1 x6 >= 2 : 27 28 ~;
pol 10 29 +;
output NONE ;
conclusion UNSAT : 30;
end pseudo-Boolean proof;
"

/-- The PB encoding of `C_9` 2-colouring is unsatisfiable — kernel-checked. -/
theorem c9_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      (((cycleSig 9).monotonicity ++ cycleUser 9 c9Edges).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 9 c9KernelProof (by native_decide)

/-- **The odd cycle `C_9` is not 2-colourable.** -/
theorem c9_2col_unsat : ¬ c9_2col.isSatisfiableInt :=
  cycle_2col_unsat 9 c9Edges c9_formulaUnsat

end CSP.L2S.PB.OddCycle
