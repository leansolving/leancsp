import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Tests.lean.«36_paley»

namespace CSP.L2S.PB.Paley

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the Paley-graph corpus CSP `paley_13_4`

This is the **first cardinality consumer** (`at_most_k` / `at_least_k`) of the PB
pipeline, and the first end-to-end result that certifies a genuine combinatorial
theorem: the **independence number** of the Paley graph `Paley(13)` is at most `3`.

The corpus CSP `paley_13_4` (`Tests/lean/36_paley.lean`) selects a subset of the
13 vertices (one Boolean `{0,1}` variable each) subject to:

* for every edge `{u,v}` (`v − u` a nonzero quadratic residue mod 13),
  `at_most_k [u,v] 1`, i.e. `x_u + x_v ≤ 1` — the two endpoints are not both in;
* `at_least_k [0..12] 4`, i.e. `Σ x_i ≥ 4` — the selected set has size ≥ 4.

A solution would be an independent set of size 4.  Since `α(Paley(13)) = 3`
(Paley graphs are self-complementary, `α = ω ≤ √13 < 4`), the CSP is
**unsatisfiable** — which is exactly the upper bound `α(Paley(13)) ≤ 3`.  These are
veripb's `Paley_p` benchmarks.

Every constraint is **linear over `{0,1}`**: each `at_most_k [u,v] 1` is `x_u + x_v
≤ 1`, and the size bound `Σ x_i ≥ 4` is the linear `≤` fact `Σ (−1)·x_i ≤ −4`.
So the proof rides the existing `encodeLinear` fragment through the clean
`unsat_of_pb` spine (`Adapter.lean`) — no auxiliary variables, no order-encoding
monotonicity (every domain is width-1).

The key structural fact that tames the corpus's `flatMap`/`filterMap`-generated
edge list is that it reduces **definitionally** to an explicit `List.map` over the
edge-pair list (`corpus_edges_eq`, by `rfl`), so edge-constraint membership is the
uniform `List.mem_map`, not 39 hand-navigated `flatMap` proofs.
-/

/-! ### The edge set and the linear constraint list -/

/-- The 39 edges of `Paley(13)`: pairs `u < v` with `v − u` a nonzero quadratic
    residue mod 13 (`{1,3,4,9,10,12}`).  Listed in the corpus generation order
    (`u` ascending, then `v` ascending), so it matches `paley_edge_constraints 13`
    definitionally. -/
def paleyEdges : List (Fin 13 × Fin 13) :=
  [(0,1),(0,3),(0,4),(0,9),(0,10),(0,12),
   (1,2),(1,4),(1,5),(1,10),(1,11),
   (2,3),(2,5),(2,6),(2,11),(2,12),
   (3,4),(3,6),(3,7),(3,12),
   (4,5),(4,7),(4,8),
   (5,6),(5,8),(5,9),
   (6,7),(6,9),(6,10),
   (7,8),(7,10),(7,11),
   (8,9),(8,11),(8,12),
   (9,10),(9,12),
   (10,11),
   (11,12)]

/-- Each edge `{u,v}` as the linear `≤` constraint `x_u + x_v ≤ 1`. -/
def edgeToLin (p : Fin 13 × Fin 13) : List (Int × Fin 13) × Int :=
  ([(1, p.1), (1, p.2)], 1)

/-- The size bound `Σ x_i ≥ 4` as the linear `≤` constraint `Σ (−1)·x_i ≤ −4`. -/
def sizeToLin : List (Int × Fin 13) × Int :=
  ([(-1, (0:Fin 13)), (-1, 1), (-1, 2), (-1, 3), (-1, 4), (-1, 5), (-1, 6),
    (-1, 7), (-1, 8), (-1, 9), (-1, 10), (-1, 11), (-1, 12)], -4)

/-- The full linear `≤` constraint list: one `≤ 1` per edge, plus the `Σ ≤ −4`
    size bound. -/
def paleyLin : List (List (Int × Fin 13) × Int) :=
  paleyEdges.map edgeToLin ++ [sizeToLin]

/-! ### Corpus structural identities (definitional) -/

/-- The corpus edge constraints are exactly the `at_most_k [u,v] 1` over `paleyEdges`
    — by `rfl`, since the corpus `flatMap`/`filterMap` over the concrete range 13
    reduces definitionally and `listToFinVector [u,v] 13` matches `⟨#[u,v], rfl⟩`. -/
theorem corpus_edges_eq :
    paley_edge_constraints 13
      = paleyEdges.map (fun p => at_most_k (⟨#[p.1, p.2], rfl⟩ :
          _root_.Vector (HomogeneousVarIndex 13) 2) 1) := rfl

/-- The corpus size constraint is `at_least_k [0..12] 4` — by `rfl`. -/
theorem corpus_size_eq :
    paley_at_least 13 4
      = [at_least_k (⟨#[0,1,2,3,4,5,6,7,8,9,10,11,12], rfl⟩ :
          _root_.Vector (HomogeneousVarIndex 13) 13) 4] := rfl

/-! ### Per-constraint bridges to the arithmetic facts -/

/-- A satisfied edge constraint `at_most_k [x,y] 1` gives `a x + a y ≤ 1`. -/
theorem pair_le_one (x y : Fin 13) (a : HomogeneousAssignment 13)
    (h : HomogeneousCSP.satisfiesConstraint
      (at_most_k (⟨#[x, y], rfl⟩ : _root_.Vector (HomogeneousVarIndex 13) 2) 1) a) :
    a x + a y ≤ 1 := by
  have := at_most_k_sat (⟨#[x, y], rfl⟩ : _root_.Vector (HomogeneousVarIndex 13) 2) 1 a h
  simpa using this

/-- A satisfied size constraint `at_least_k [0..12] 4` gives `4 ≤ Σ a i`. -/
theorem size_ge_four (a : HomogeneousAssignment 13)
    (h : HomogeneousCSP.satisfiesConstraint
      (at_least_k (⟨#[0,1,2,3,4,5,6,7,8,9,10,11,12], rfl⟩ :
        _root_.Vector (HomogeneousVarIndex 13) 13) 4) a) :
    (4 : ℤ) ≤ a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 + a 11 + a 12 := by
  have := at_least_k_sat (⟨#[0,1,2,3,4,5,6,7,8,9,10,11,12], rfl⟩ :
    _root_.Vector (HomogeneousVarIndex 13) 13) 4 a h
  simp only [Nat.cast_ofNat] at this
  simp at this
  linarith

/-! ### The signature and the linear `≤` facts from any solution -/

/-- The PB signature: 13 integer variables, each over the Boolean domain `{0,1}`. -/
def paleySig : CSPSig where
  nInt := 13
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 0 1
  sorted := fun _ => domainValues_sorted 0 1
  nonempty := fun _ => domainValues_nonempty (by norm_num)

/-- The bound bridge data for `unsat_of_pb`: every variable is in `[0,1]`. -/
theorem paley_hbound (i : Fin paley_13_4.num_vars) :
    bound i 0 1 ∈ paley_13_4.constraints := by
  show bound i 0 1 ∈ paley_bounds 13 ++ paley_edge_constraints 13 ++ paley_at_least 13 4
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩

/-- Every linear `≤` fact in `paleyLin` follows from any solution. -/
theorem paley_hlin (a : HomogeneousAssignment 13) (hsol : paley_13_4.isSolution a) :
    ∀ c ∈ paleyLin, (c.1.map (fun p => p.1 * a p.2)).sum ≤ c.2 := by
  intro c hc
  rw [paleyLin, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨p, hp, rfl⟩ | hc
  · -- edge constraint
    have hmem : at_most_k (⟨#[p.1, p.2], rfl⟩ : _root_.Vector (HomogeneousVarIndex 13) 2) 1
        ∈ paley_13_4.constraints := by
      show _ ∈ paley_bounds 13 ++ paley_edge_constraints 13 ++ paley_at_least 13 4
      apply List.mem_append_left
      apply List.mem_append_right
      rw [corpus_edges_eq]
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have hpair := pair_le_one p.1 p.2 a (hsol _ hmem)
    simp only [edgeToLin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    linarith
  · -- size constraint
    rw [List.mem_singleton] at hc
    subst hc
    have hmem : at_least_k (⟨#[0,1,2,3,4,5,6,7,8,9,10,11,12], rfl⟩ :
        _root_.Vector (HomogeneousVarIndex 13) 13) 4 ∈ paley_13_4.constraints := by
      show _ ∈ paley_bounds 13 ++ paley_edge_constraints 13 ++ paley_at_least 13 4
      apply List.mem_append_right
      rw [corpus_size_eq]
      exact List.mem_cons_self
    have hsize := size_ge_four a (hsol _ hmem)
    simp only [sizeToLin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    linarith

/-! ### The certificate and the end-to-end theorem -/

/-- The veripb-elaborated kernel proof of UNSAT for `paleyLin`'s OPB serialization
    (RoundingSat + veripb; both untrusted).  The 13 thresholds map to OPB `x1..x13`, where
    `xᵢ = ⟦vertex (i−1) = 0⟧` is the complement of vertex `(i−1)`'s set-membership; so an
    edge bound `x_u + x_v ≤ 1` appears as `xᵤ + xᵥ ≥ 1` (a vertex-cover clause) and the size
    bound `Σ vertexᵢ ≥ 4` as `Σ ~xᵢ ≥ 4`.  The cutting-planes refutation (no cover of size
    ≤ 9, i.e. `τ(Paley(13)) = 10`) uses `pbc`/`subproof` redundancy and division. -/
def paleyKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 40;
rup >= 0 : ~ ;
pbc 1000000000000000 x10 1000000000000000 x13 1000000000000000 x9 >= 2000000000000000 : subproof
pol 42 33 1000000000000000 * + 35 1000000000000000 * + 37 1000000000000000 * + 1000000000000000 d;
pol 42 43 1000000000000000 * +;
qed : 44;
pbc 1000000000000000 x10 1000000000000000 x13 1000000000000000 x9 >= 2000000000000000 : subproof
pol 46 33 1000000000000000 * + 35 1000000000000000 * + 37 1000000000000000 * + 1000000000000000 d;
pol 46 47 1000000000000000 * +;
qed : 48;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 50 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 50 51 500000000000000 * +;
qed : 52;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 54 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 54 55 500000000000000 * +;
qed : 56;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 58 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 58 59 500000000000000 * +;
qed : 60;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 62 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 62 63 500000000000000 * +;
qed : 64;
pbc 1000000000000000 x10 1000000000000000 x13 1000000000000000 x9 >= 2000000000000000 : subproof
pol 66 33 1000000000000000 * + 35 1000000000000000 * + 37 1000000000000000 * + 1000000000000000 d;
pol 66 67 1000000000000000 * +;
qed : 68;
pbc 1000000000000000 x10 1000000000000000 x13 1000000000000000 x9 >= 2000000000000000 : subproof
pol 70 33 1000000000000000 * + 35 1000000000000000 * + 37 1000000000000000 * + 1000000000000000 d;
pol 70 71 1000000000000000 * +;
qed : 72;
pbc 1000000000000000 x10 1000000000000000 x13 1000000000000000 x9 >= 2000000000000000 : subproof
pol 74 33 1000000000000000 * + 35 1000000000000000 * + 37 1000000000000000 * + 1000000000000000 d;
pol 74 75 1000000000000000 * +;
qed : 76;
pbc 1000000000000000 x10 1000000000000000 x13 1000000000000000 x9 >= 2000000000000000 : subproof
pol 78 33 1000000000000000 * + 35 1000000000000000 * + 37 1000000000000000 * + 1000000000000000 d;
pol 78 79 1000000000000000 * +;
qed : 80;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 82 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 82 83 500000000000000 * +;
qed : 84;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 86 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 86 87 500000000000000 * +;
qed : 88;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 90 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 90 91 500000000000000 * +;
qed : 92;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 94 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 94 95 500000000000000 * +;
qed : 96;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 98 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 98 99 500000000000000 * +;
qed : 100;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 102 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 102 103 500000000000000 * +;
qed : 104;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 106 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 106 107 500000000000000 * +;
qed : 108;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 110 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 110 111 500000000000000 * +;
qed : 112;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 114 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 114 115 500000000000000 * +;
qed : 116;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 118 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 118 119 500000000000000 * +;
qed : 120;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 122 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 122 123 500000000000000 * +;
qed : 124;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 126 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 126 127 500000000000000 * +;
qed : 128;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 130 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 130 131 500000000000000 * +;
qed : 132;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 134 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 134 135 500000000000000 * +;
qed : 136;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 138 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 138 139 500000000000000 * +;
qed : 140;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 142 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 142 143 500000000000000 * +;
qed : 144;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 146 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 146 147 500000000000000 * +;
qed : 148;
pbc 500000000000000 x10 500000000000000 x13 500000000000000 x9 >= 1000000000000000 : subproof
pol 150 33 500000000000000 * + 35 500000000000000 * + 37 500000000000000 * + 500000000000000 d;
pol 150 151 500000000000000 * +;
qed : 152;
pol 45 ~x9 0 * + ~x10 0 * + ~x13 0 * + 2 d 500000000000000 d;
pol 45 ~x9 0 * + ~x10 0 * + ~x13 0 * + 2 d 500000000000000 d;
pol 30 40 + 15 + 14 + 13 + x1 + s;
pol 40 34 + 30 + 25 + x1 + x7 + s;
pol 41 1 1000000000000000 * + 2 1000000000000000 * + 24 1000000000000000 * + 32 1000000000000000 * + 40 1000000000000000 * + 157 1000000000000000 * + s 156 1000000000000000 * + s 6 1000000000000000 * + s 5 1000000000000000 * + s 4 1000000000000000 * + s 3 1000000000000000 * + s 2 1000000000000000 * + s 1 1000000000000000 * + s 1862646 d 536870667 d;
pol 32 40 + 158 +;
pol 24 159 +;
pol 37 160 +;
pol 40 158 + 38 + 36 + 31 + 29 + 161 3 * + s x13 + x6 + s;
pol 38 40 + 158 +;
pol 26 163 + 20 + 19 + 18 + s 162 + s;
pol 163 37 +;
pol 39 40 + 158 + 29 + 28 + 165 + 22 2 * + s 21 + 17 + s 164 + s;
pol 41 1 1000000000000000 * + 18 500000000000000 * + 19 500000000000000 * + 27 500000000000000 * + 37 1000000000000000 * + 40 1000000000000000 * + s 11 500000000000000 * + 10 500000000000000 * + s 9 500000000000000 * + s 8 500000000000000 * + s 166 500000000000000 * + s 931323 d 536870667 d;
pol 41 1 1000000000000000 * + 18 500000000000000 * + 19 500000000000000 * + 27 500000000000000 * + 37 1000000000000000 * + 40 1000000000000000 * + s 931323 d 536870667 d;
pol 22 163 +;
pol 22 40 + 158 + 36 + 16 + 15 + 14 + s 13 + s 12 + s 7 + s 167 + s;
rup 1 x5 >= 1 : ~ 170 23;
rup 1 x6 >= 1 : ~ 170 25;
rup 1 x8 >= 1 : ~ 170 30;
rup 1 x10 >= 1 : ~ 170 33;
rup 1 x12 >= 1 : ~ 170 34;
rup 1 x13 >= 1 : ~ 170 35;
rup 1 x5 1 x10 1 x13 1 x6 1 x8 1 x9 >= 5 : 171 173 176 172 174 ~;
pol 12 163 + 177 +;
rup 1 x5 1 x10 1 x13 1 ~x9 >= 4 : 170 171 174 176 ~;
pol 157 179 + 29 + 18 + s 14 + s 178 + s;
rup 1 x3 >= 1 : ~ 180 7;
rup 1 x11 >= 1 : ~ 180 10;
rup 1 ~x7 >= 1 : ~ 182 173 181 176 174 172 175 158 171 40;
rup 1 ~x4 >= 1 : ~ 182 173 181 176 174 172 175 158 171 40;
rup 1 ~x4 1 ~x7 >= 2 : 184 183 ~;
pol 18 185 +;
output NONE ;
conclusion UNSAT : 186;
end pseudo-Boolean proof;
"

/-- The PB encoding of the Paley independent-set query is unsatisfiable — established by the
    external PB certificate, kernel-checked through PBLean's verified reflection checker
    (`native_decide` runs the checker; RoundingSat / veripb / the serializer are untrusted). -/
theorem paley_formulaUnsat :
    VeriPB.Reflect.formulaUnsat
      ((encodeLinear paleySig paleyLin).toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 13 paleyKernelProof (by native_decide)

/-- **End-to-end Paley-graph UNSAT.** The corpus CSP `paley_13_4` — does `Paley(13)`
    have an independent set of size 4? — is unsatisfiable, certifying
    `α(Paley(13)) ≤ 3`.  Discharged through the verified PB pipeline: the cardinality
    bridges turn any solution into 39 edge inequalities `x_u + x_v ≤ 1` plus the size
    bound `Σ x_i ≥ 4`, the `unsat_of_pb` spine order-encodes them via `encodeLinear`,
    and the committed certificate `paley_formulaUnsat` contradicts it. -/
theorem paley_13_4_unsat : ¬ paley_13_4.isSatisfiable := by
  refine unsat_of_pb paley_13_4 (fun _ => 0) (fun _ => 1) (fun _ => by norm_num)
    paley_hbound paleyLin paley_hlin ?_
  show VeriPB.Reflect.formulaUnsat
    ((encodeLinear paleySig paleyLin).toArray.map PBConstr.toNatConstr)
  exact paley_formulaUnsat

end CSP.L2S.PB.Paley
