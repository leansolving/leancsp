import CSP.L2S.Backends.PB.Compose
import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Backends.PB.LinearNe
import CSP.L2S.Backends.PB.Cardinality

namespace CSP.L2S.PB

open CSPSig
open CSP.L2S

/-!
# PB backend — the per-pattern `EncConstr` library

One smart constructor `enc<Pattern> : … → EncConstr S` per supported constraint
pattern, packaging its encoding together with its soundness and reusing the
verified `extend_sat_*` / `encode*_sound` bridges.  The `pre` field is the
arithmetic fact the constraint produces (a linear `≤`, `Nodup`, a disequality, …).

Aux-free entries set `setsAux := fun _ => []`; the only aux user is `encLinearNe`,
which owns one selector index.  These compose through `csp_unsat_of_enc_alloc`
into a single `formulaUnsat ⇒ ¬ satisfiable` theorem.
-/

variable {S : CSPSig}

/-- Under `extend`, the recovered values agree with the assignment inside any linear
    term list (the `extend_intValue` rewrite, lifted to a coefficient·variable list). -/
theorem map_intValue_extend (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (terms : List (Int × Fin S.nInt)) :
    (terms.map (fun p => p.1 * (extend a bA auxA).intValue p.2))
      = terms.map (fun p => p.1 * a p.2) :=
  List.map_congr_left (fun p _ => by rw [extend_intValue a bA auxA hdom p.2])

/-! ### Linear comparisons -/

/-- `Σ aᵢ·xᵢ ≤ b`. -/
def encLinearLe (terms : List (Int × Fin S.nInt)) (b : Int) : EncConstr S where
  constrs := (normalize (encodeLinearLe terms b)).toList
  pre := fun a => (terms.map (fun p => p.1 * a p.2)).sum ≤ b
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hle _ c hc
    rw [Option.mem_toList] at hc
    exact extend_sat_encodeLinearLe a bA auxA hdom terms b c hc hle

/-- `Σ aᵢ·xᵢ ≥ b`. -/
def encLinearGe (terms : List (Int × Fin S.nInt)) (b : Int) : EncConstr S where
  constrs := (normalize (encodeLinearGe terms b)).toList
  pre := fun a => b ≤ (terms.map (fun p => p.1 * a p.2)).sum
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hge _ c hc
    rw [Option.mem_toList] at hc
    rw [← normalize_sat_iff _ _ hc]
    apply encodeLinearGe_sound
    rw [map_intValue_extend a bA auxA hdom terms]; exact hge

/-- `Σ aᵢ·xᵢ < b` (integer-strict). -/
def encLinearLt (terms : List (Int × Fin S.nInt)) (b : Int) : EncConstr S where
  constrs := (normalize (encodeLinearLt terms b)).toList
  pre := fun a => (terms.map (fun p => p.1 * a p.2)).sum < b
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hlt _ c hc
    rw [Option.mem_toList] at hc
    rw [← normalize_sat_iff _ _ hc]
    apply encodeLinearLt_sound
    rw [map_intValue_extend a bA auxA hdom terms]; exact hlt

/-- `Σ aᵢ·xᵢ > b` (integer-strict). -/
def encLinearGt (terms : List (Int × Fin S.nInt)) (b : Int) : EncConstr S where
  constrs := (normalize (encodeLinearGt terms b)).toList
  pre := fun a => b < (terms.map (fun p => p.1 * a p.2)).sum
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hgt _ c hc
    rw [Option.mem_toList] at hc
    rw [← normalize_sat_iff _ _ hc]
    apply encodeLinearGt_sound
    rw [map_intValue_extend a bA auxA hdom terms]; exact hgt

/-- `Σ aᵢ·xᵢ = b` (emits the `≤` and `≥` halves). -/
def encLinearEq (terms : List (Int × Fin S.nInt)) (b : Int) : EncConstr S where
  constrs := (encodeLinearEq terms b).filterMap normalize
  pre := fun a => (terms.map (fun p => p.1 * a p.2)).sum = b
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom heq _ c hc
    rw [List.mem_filterMap] at hc
    obtain ⟨sc, hmem, hnorm⟩ := hc
    rw [← normalize_sat_iff _ _ hnorm]
    refine encodeLinearEq_sound (extend a bA auxA) terms b ?_ sc hmem
    rw [map_intValue_extend a bA auxA hdom terms]; exact heq

/-! ### `alldifferent`, `ne`, `ne_const`, `eq_const` -/

/-- `alldifferent` over `vars` with value list `D` (the union of the domains). -/
def encAllDifferent (vars : List (Fin S.nInt)) (D : List Int) : EncConstr S where
  constrs := (encodeAllDifferent vars D).filterMap normalize
  pre := fun a => (vars.map a).Nodup
  setsAux := fun _ => []
  sound := fun a bA auxA hdom hnd _ c hc =>
    extend_sat_encodeAllDifferent a bA auxA hdom vars D c hc hnd

/-- `xⱼ ≠ val` (aux-free order-encoding indicator). -/
def encNeConst (j : Fin S.nInt) (val : Int) : EncConstr S where
  constrs := (normalize (encodeNeConst j val)).toList
  pre := fun a => a j ≠ val
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hne _ c hc
    rw [Option.mem_toList] at hc
    exact extend_sat_encodeNeConst a bA auxA hdom j val hne c hc

/-- `xⱼ = c`, encoded as the linear equality `1·xⱼ = c`. -/
def encEqConst (j : Fin S.nInt) (c : Int) : EncConstr S where
  constrs := (encodeLinearEq [(1, j)] c).filterMap normalize
  pre := fun a => a j = c
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom heq _ d hc
    rw [List.mem_filterMap] at hc
    obtain ⟨sc, hmem, hnorm⟩ := hc
    rw [← normalize_sat_iff _ _ hnorm]
    refine encodeLinearEq_sound (extend a bA auxA) [(1, j)] c ?_ sc hmem
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero,
      extend_intValue a bA auxA hdom j]
    exact heq

/-! ### not-all-equal (`schur_triple` and its k-ary generalization) -/

/-- not-all-equal over a binary (`{c0, c1}`) domain. -/
def encNotAllEqualBin (vars : List (Fin S.nInt)) (hw : ∀ i ∈ vars, 0 < S.width i)
    (c0 c1 : Int) (hdomvals : ∀ i ∈ vars, S.values i = [c0, c1]) : EncConstr S where
  constrs := (encodeNotAllEqualBin vars hw).filterMap normalize
  pre := fun a => ∃ i ∈ vars, ∃ i' ∈ vars, a i ≠ a i'
  setsAux := fun _ => []
  sound := fun a bA auxA hdom hne _ c hc =>
    extend_sat_encodeNotAllEqualBin a bA auxA hdom vars hw c0 c1 hdomvals hne c hc

/-- not-all-equal over an arbitrary value list `D` (k>2 colours). -/
def encNotAllEqualMulti (vars : List (Fin S.nInt)) (D : List Int) : EncConstr S where
  constrs := (encodeNotAllEqualMulti vars D).filterMap normalize
  pre := fun a => ∃ i ∈ vars, ∃ i' ∈ vars, a i ≠ a i'
  setsAux := fun _ => []
  sound := fun a bA auxA hdom hne _ c hc =>
    extend_sat_encodeNotAllEqualMulti a bA auxA hdom vars D hne c hc

/-- `xᵢ ≠ xⱼ` (graph-colouring edge), as `alldifferent` over the pair `[i, j]`. -/
def encNotEqual (i j : Fin S.nInt) (D : List Int) : EncConstr S where
  constrs := (encodeAllDifferent [i, j] D).filterMap normalize
  pre := fun a => a i ≠ a j
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hij _ c hc
    refine extend_sat_encodeAllDifferent a bA auxA hdom [i, j] D c hc ?_
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_singleton,
      List.not_mem_nil, not_false_iff, List.nodup_nil, and_true]
    exact hij

/-! ### Cardinality over `{0,1}` integer variables (via the linear path) -/

/-- The unit-coefficient term list of a scope evaluates to the plain value sum. -/
private theorem unit_terms_map (a : Fin S.nInt → Int) (scope : List (Fin S.nInt)) :
    (scope.map (fun i => ((1 : Int), i))).map (fun p => p.1 * a p.2) = scope.map a := by
  rw [List.map_map]; exact List.map_congr_left (fun i _ => by simp)

/-- `Σ xᵢ ≤ k` over a scope of `{0,1}`-valued integer variables (`at_most_k`). -/
def encAtMostK (scope : List (Fin S.nInt)) (k : Int) : EncConstr S where
  constrs := (normalize (encodeLinearLe (scope.map (fun i => ((1 : Int), i))) k)).toList
  pre := fun a => (scope.map a).sum ≤ k
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hle _ c hc
    rw [Option.mem_toList] at hc
    refine extend_sat_encodeLinearLe a bA auxA hdom (scope.map (fun i => ((1 : Int), i))) k c hc ?_
    rw [unit_terms_map]; exact hle

/-- `k ≤ Σ xᵢ` over a scope of `{0,1}`-valued integer variables (`at_least_k`). -/
def encAtLeastK (scope : List (Fin S.nInt)) (k : Int) : EncConstr S where
  constrs := (normalize (encodeLinearGe (scope.map (fun i => ((1 : Int), i))) k)).toList
  pre := fun a => k ≤ (scope.map a).sum
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hge _ c hc
    rw [Option.mem_toList] at hc
    rw [← normalize_sat_iff _ _ hc]
    apply encodeLinearGe_sound
    rw [map_intValue_extend a bA auxA hdom (scope.map (fun i => ((1 : Int), i))), unit_terms_map]
    exact hge

/-! ### Big-M disequality (`linear_ne`) — the aux-using entry -/

/-- `Σ aᵢ·xᵢ ≠ b`, owning the fresh selector index `s`. -/
def encLinearNe (terms : List (Int × Fin S.nInt)) (b : Int) (s : Fin S.nAux) : EncConstr S where
  constrs := (encodeLinearNe terms b s).filterMap normalize
  pre := fun a => (terms.map (fun p => p.1 * a p.2)).sum ≠ b
  setsAux := fun a => [(s, decide ((terms.map (fun p => p.1 * a p.2)).sum > b))]
  sound := by
    intro a bA auxA hdom hne hframe c hc
    refine extend_sat_encodeLinearNe a bA auxA hdom terms b s hne ?_ c hc
    exact hframe (s, decide ((terms.map (fun p => p.1 * a p.2)).sum > b)) (by simp)

/-! ### The `HomogeneousCSP` entry point -/

/-- **CSP UNSAT via a composed encoding.**  Given per-variable `bound`
    constraints, a list of `EncConstr` whose preconditions follow from any solution
    (`hpre`), pairwise-distinct owned aux indices (`hnd`), and a `formulaUnsat`
    certificate over the combined formula, the CSP is unsatisfiable.  Generalizes
    the linear-only `unsat_of_pb` to the whole `EncConstr` library. -/
theorem unsat_of_encoding (csp : IntCSP) (lb ub : Fin csp.num_vars → ℤ)
    (hle : ∀ i, lb i ≤ ub i)
    (hbound : ∀ i, bound i (lb i) (ub i) ∈ csp.constraints)
    (es : List (EncConstr (toCSPSig csp lb ub hle)))
    (hpre : ∀ a, csp.isSolutionInt a → ∀ e ∈ es, e.pre a)
    (hnd : ∀ a, ((es.flatMap (·.setsAux a)).map Prod.fst).Nodup)
    (hunsat : VeriPB.Reflect.formulaUnsat
        (((toCSPSig csp lb ub hle).monotonicity ++ EncConstr.combine es).toArray.map
          PBConstr.toNatConstr)) :
    ¬ csp.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  refine csp_unsat_of_enc_alloc (toCSPSig csp lb ub hle) es hnd hunsat ⟨a, ?_, hpre a hsol⟩
  intro i
  show a i ∈ domainValues (lb i) (ub i)
  rw [mem_domainValues]
  exact bound_sat i (lb i) (ub i) a (hsol _ (hbound i))

end CSP.L2S.PB
