import CSP.L2S.Backends.PB.Library
import CSP.L2S.Backends.PB.LexLeader

namespace CSP.L2S.PB

open CSP.L2S
open scoped BigOperators

/-!
# PB backend — the single generic `csp_unsat`

This file closes the loop: a **one-theorem** `CSP-SAT ⇒ PB-SAT` pipeline that takes a
`IntCSP` and a kernel-checked PB UNSAT certificate and concludes `¬ csp.isSatisfiableInt`,
with no per-instance soundness glue.

* `cspSig csp` — the order-encoding signature derived from `csp`'s `bound` constraints
  (`extractVariableBounds`), one integer variable per CSP variable.
* `encodePattern S c` — dispatch on the finite `IntConstraint` inductive to the matching
  `EncConstr` from `Library.lean`; unsupported patterns encode to `[]` (sound: dropping a
  constraint only weakens the PB formula).  The raw `ℕ` pattern indices are converted to
  `Fin S.nInt` by `toFinList`, guarded by a decidable in-range check so the soundness link
  needs no external well-formedness hypothesis.
* `encodePattern_sound` — for every emitted entry, its arithmetic precondition follows
  from `patternHolds c a` (which *is* `satisfiesConstraintInt`).  This is the generic
  Step-A bridge, replacing the per-instance `*_sat` lemmas.
* `csp_unsat csp cert` — assemble: a solution gives `patternHolds` for each constraint,
  hence each entry's precondition; the composition spine (`csp_unsat_of_encfree`) plus the
  certificate close the goal.  In-domain comes from the `bound` constraints.
-/

variable {S : CSPSig}

/-! ### The derived signature -/

/-- Lower bound of variable `i`, read from its `bound` constraint (default `-1000`). -/
def cspLb (csp : IntCSP) (i : Fin csp.num_vars) : ℤ := (csp.extractVariableBounds i).1

/-- Upper bound of variable `i`; `max`'d with the lower bound so `cspLb ≤ cspUb` holds
    unconditionally (for well-formed bounds `lb ≤ ub` this is just the stored `ub`). -/
def cspUb (csp : IntCSP) (i : Fin csp.num_vars) : ℤ :=
  max (cspLb csp i) (csp.extractVariableBounds i).2

theorem cspLb_le_cspUb (csp : IntCSP) (i : Fin csp.num_vars) : cspLb csp i ≤ cspUb csp i :=
  le_max_left _ _

/-- `pairAux n = n·(n−1)/2`, recursively: the number of unordered pairs of `n` items
    (the selectors an `alldifferentOffset`'s pairwise Big-M expansion owns). -/
def pairAux : ℕ → ℕ
  | 0 => 0
  | n + 1 => n + pairAux n

/-- Number of auxiliary selector variables a single constraint's encoding owns: one for a
    Big-M general disequality (`linear`/`sum`/`*_rel_var` with op `.NE`), a pairwise block
    for the offset all-different.  Everything else is aux-free. -/
def auxCount {n : ℕ} : IntConstraint n → ℕ
  | .linear _ _ .NE _ => 1
  | .sum _ .NE _ => 1
  | .sum_rel_var _ .NE _ => 1
  | .linear_rel_var _ _ .NE _ => 1
  | .alldifferentOffset vars offsets => pairAux (min vars.length offsets.length)
  | .abs_diff_rel _ _ .GE _ => 1
  | .abs_diff_rel _ _ .GT _ => 1
  | .abs_diff_rel _ _ .EQ _ => 1
  | .abs_diff_rel _ _ .NE _ => 2
  | .abs_diff_var _ _ _ => 1
  | .strictLexRevLeader => 1
  | _ => 0

/-- Total auxiliary count of a CSP: the selectors its constraints' encodings own. -/
def cspNAux (csp : IntCSP) : ℕ := (csp.constraints.map auxCount).sum

/-- The order-encoding signature derived from `csp`'s bounds, sized to hold the Big-M
    selector variables (`nAux := cspNAux csp`).  Aux-free CSPs have `cspNAux = 0`, so for
    them this is definitionally the old `nAux = 0` signature (committed certificates stay
    valid). -/
def cspSig (csp : IntCSP) : CSPSig :=
  { toCSPSig csp (cspLb csp) (cspUb csp) (cspLb_le_cspUb csp) with nAux := cspNAux csp }

@[simp] theorem cspSig_nInt (csp : IntCSP) : (cspSig csp).nInt = csp.num_vars := rfl
@[simp] theorem cspSig_values (csp : IntCSP) (i : Fin csp.num_vars) :
    (cspSig csp).values i = domainValues (cspLb csp i) (cspUb csp i) := rfl

/-! ### `ℕ → Fin` index conversion -/

/-- Convert a list of raw `ℕ` pattern indices to `Fin S.nInt`, dropping out-of-range
    indices (which never occur in well-formed CSPs). -/
def toFinList (S : CSPSig) (vars : List ℕ) : List (Fin S.nInt) :=
  vars.filterMap (fun v => if h : v < S.nInt then some ⟨v, h⟩ else none)

/-- On in-range indices, mapping the assignment over the converted list agrees with the
    `valAt`-reading of the original `ℕ` list (the bridge from `patternHolds` to `pre`). -/
theorem toFinList_map (a : Fin S.nInt → Int) (vars : List ℕ)
    (hwf : ∀ v ∈ vars, v < S.nInt) :
    (toFinList S vars).map a = vars.map (valAt a) := by
  unfold toFinList
  induction vars with
  | nil => simp
  | cons x xs ih =>
    have hx : x < S.nInt := hwf x (by simp)
    have ih' := ih (fun v hv => hwf v (by simp [hv]))
    simp only [List.filterMap_cons, hx, dite_true, List.map_cons, ih', valAt]

/-- The value list used for `alldifferent`/`ne`/`schur` encodings: the union of the
    variables' domains. -/
def domOf (S : CSPSig) (vars : List (Fin S.nInt)) : List Int :=
  (vars.flatMap (fun i => S.values i)).dedup

/-! ### Linear / cardinality relations via a single dispatcher -/

/-- Encode a relation `Σ termᵢ (op) target` to the matching linear encoder.  `≠`
    (which needs a fresh aux variable) encodes to `[]` for now. -/
def encodeRel (S : CSPSig) (op : RelOp) (terms : List (Int × Fin S.nInt))
    (target : Int) : List (EncConstr S) :=
  match op with
  | .LE => [encLinearLe terms target]
  | .GE => [encLinearGe terms target]
  | .LT => [encLinearLt terms target]
  | .GT => [encLinearGt terms target]
  | .EQ => [encLinearEq terms target]
  | .NE => []

/-- Every `encodeRel` entry is aux-free. -/
theorem encodeRel_setsAux (op : RelOp) (terms : List (Int × Fin S.nInt)) (target : Int)
    (a : Fin S.nInt → Int) (e : EncConstr S) (he : e ∈ encodeRel S op terms target) :
    e.setsAux a = [] := by
  cases op <;> simp only [encodeRel] at he
  case NE => exact absurd he (by simp)
  all_goals (rw [List.mem_singleton] at he; subst he; rfl)

/-- `encodeRel` soundness: the arithmetic relation on the assignment gives every
    emitted entry's precondition. -/
theorem encodeRel_sound (op : RelOp) (terms : List (Int × Fin S.nInt)) (target : Int)
    (a : Fin S.nInt → Int)
    (hpat : relHolds op (terms.map (fun p => p.1 * a p.2)).sum target)
    (e : EncConstr S) (he : e ∈ encodeRel S op terms target) : e.pre a := by
  cases op <;> simp only [encodeRel] at he
  case NE => exact absurd he (by simp)
  all_goals (rw [List.mem_singleton] at he; subst he; exact hpat)

/-- Like `encodeRel`, but `≠` is encoded by the Big-M `encLinearNe` owning the selector
    index `base` (dropped, soundly, if `base` is out of range — which never happens once
    `nAux` is sized by `cspNAux`). -/
def encodeRelAt (S : CSPSig) (base : ℕ) (op : RelOp) (terms : List (Int × Fin S.nInt))
    (target : Int) : List (EncConstr S) :=
  match op with
  | .LE => [encLinearLe terms target]
  | .GE => [encLinearGe terms target]
  | .LT => [encLinearLt terms target]
  | .GT => [encLinearGt terms target]
  | .EQ => [encLinearEq terms target]
  | .NE => if h : base < S.nAux then [encLinearNe terms target ⟨base, h⟩] else []

/-- `encodeRelAt` soundness: the arithmetic relation gives every emitted entry's
    precondition (the `≠` entry's precondition is exactly `relHolds .NE`). -/
theorem encodeRelAt_sound (base : ℕ) (op : RelOp) (terms : List (Int × Fin S.nInt))
    (target : Int) (a : Fin S.nInt → Int)
    (hpat : relHolds op (terms.map (fun p => p.1 * a p.2)).sum target)
    (e : EncConstr S) (he : e ∈ encodeRelAt S base op terms target) : e.pre a := by
  cases op <;> simp only [encodeRelAt] at he
  case NE =>
    split at he
    · rw [List.mem_singleton] at he; subst he
      show (terms.map (fun p => p.1 * a p.2)).sum ≠ target
      exact hpat
    · exact absurd he (by simp)
  all_goals (rw [List.mem_singleton] at he; subst he; exact hpat)

/-- The linear term list `coeffs · (toFinList vars)` sums to the `patternHolds`
    `zipWith`-form on in-range indices. -/
theorem linTerms_sum (a : Fin S.nInt → Int) (coeffs : List Int) (vars : List ℕ)
    (hwf : ∀ v ∈ vars, v < S.nInt) :
    ((coeffs.zip (toFinList S vars)).map (fun p => p.1 * a p.2)).sum
      = (List.zipWith (· * ·) coeffs (vars.map (valAt a))).sum := by
  rw [List.map_zip_eq_zipWith, ← toFinList_map a vars hwf, List.zipWith_map_right]; rfl

/-- The unit-coefficient term list of `toFinList vars` sums to the plain value sum. -/
theorem unitTerms_sum (a : Fin S.nInt → Int) (vars : List ℕ)
    (hwf : ∀ v ∈ vars, v < S.nInt) :
    (((toFinList S vars).map (fun v => ((1 : Int), v))).map (fun p => p.1 * a p.2)).sum
      = (vars.map (valAt a)).sum := by
  have h1 : ((toFinList S vars).map (fun v => ((1 : Int), v))).map (fun p => p.1 * a p.2)
      = (toFinList S vars).map a := by
    rw [List.map_map]; exact List.map_congr_left (fun v _ => by simp)
  rw [h1, toFinList_map a vars hwf]

/-! ### Helpers for the trivial linear constructors -/

/-- Shift a relation across subtraction: `op` of a difference vs `0` iff `op` of the
    two sides.  Lets a binary/var-target comparison be encoded as `lhs − rhs (op) 0`. -/
theorem relHolds_sub_zero (op : RelOp) (x y : Int) :
    relHolds op (x - y) 0 ↔ relHolds op x y := by
  cases op <;> simp only [relHolds] <;> omega

/-- The two-term list `[(1,i), (-1,j)]` sums to `a i − a j`. -/
theorem binTerms_sum (a : Fin S.nInt → Int) (i j : Fin S.nInt) :
    ([((1 : Int), i), ((-1 : Int), j)].map (fun p => p.1 * a p.2)).sum = a i - a j := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- The one-term list `[(1,i)]` sums to `a i`. -/
theorem unaryTerms_sum (a : Fin S.nInt → Int) (i : Fin S.nInt) :
    ([((1 : Int), i)].map (fun p => p.1 * a p.2)).sum = a i := by
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; ring

/-- Appending a `−1`-coefficient term subtracts that variable from the sum. -/
theorem appendNeg_sum (a : Fin S.nInt → Int) (terms : List (Int × Fin S.nInt))
    (t : Fin S.nInt) :
    ((terms ++ [((-1 : Int), t)]).map (fun p => p.1 * a p.2)).sum
      = (terms.map (fun p => p.1 * a p.2)).sum - a t := by
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]; ring

/-- Soundness for a binary comparison `i (op) j` encoded as `i − j (op) 0`. -/
theorem encodeRel_bin_sound (op : RelOp) (i j : Fin S.nInt) (a : Fin S.nInt → Int)
    (hpat : relHolds op (a i) (a j)) (e : EncConstr S)
    (he : e ∈ encodeRel S op [((1 : Int), i), ((-1 : Int), j)] 0) : e.pre a := by
  refine encodeRel_sound op _ 0 a ?_ e he
  rw [binTerms_sum, relHolds_sub_zero]; exact hpat

/-- Soundness for a unary comparison `i (op) c` encoded as the singleton term list. -/
theorem encodeRel_unary_sound (op : RelOp) (i : Fin S.nInt) (c : Int) (a : Fin S.nInt → Int)
    (hpat : relHolds op (a i) c) (e : EncConstr S)
    (he : e ∈ encodeRel S op [((1 : Int), i)] c) : e.pre a := by
  refine encodeRel_sound op _ c a ?_ e he
  rw [unaryTerms_sum]; exact hpat

/-- Soundness for a variable-target relation `Σ terms (op) (a t)`, encoded by moving the
    target variable to the LHS with coefficient `−1` (target `0`).  `hsum` identifies the
    encoded term-sum with the pattern's LHS.  Factored out so the `appendNeg_sum` /
    `relHolds_sub_zero` reasoning over a *variable* `op` is elaborated once. -/
theorem encodeRel_var_sound (op : RelOp) (terms : List (Int × Fin S.nInt)) (t : Fin S.nInt)
    (a : Fin S.nInt → Int) (lhs : Int)
    (hsum : (terms.map (fun p => p.1 * a p.2)).sum = lhs) (hpat : relHolds op lhs (a t))
    (e : EncConstr S) (he : e ∈ encodeRel S op (terms ++ [((-1 : Int), t)]) 0) : e.pre a := by
  refine encodeRel_sound op (terms ++ [((-1 : Int), t)]) 0 a ?_ e he
  rw [appendNeg_sum, hsum, relHolds_sub_zero]; exact hpat

/-- `encodeRelAt` analogue of `encodeRel_var_sound` (NE-aware, base-threaded).  Isolated so
    the `appendNeg_sum` / `relHolds_sub_zero` reasoning over a *variable* `op` is elaborated
    once rather than inside the per-constructor `cases`. -/
theorem encodeRelAt_var_sound (base : ℕ) (op : RelOp) (terms : List (Int × Fin S.nInt))
    (t : Fin S.nInt) (a : Fin S.nInt → Int) (lhs : Int)
    (hsum : (terms.map (fun p => p.1 * a p.2)).sum = lhs) (hpat : relHolds op lhs (a t))
    (e : EncConstr S) (he : e ∈ encodeRelAt S base op (terms ++ [((-1 : Int), t)]) 0) :
    e.pre a := by
  refine encodeRelAt_sound base op (terms ++ [((-1 : Int), t)]) 0 a ?_ e he
  rw [appendNeg_sum, hsum, relHolds_sub_zero]; exact hpat

/-! ### `encodePattern` -/

/-- Encode one constraint to a list of soundness-carrying `EncConstr`s.  `bound` (which
    only fixes the domain) and every unsupported pattern map to `[]`. -/
def encodePattern (S : CSPSig) : IntConstraint S.nInt → List (EncConstr S)
  | .alldifferent vars =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        [encAllDifferent (toFinList S vars) (domOf S (toFinList S vars))]
      else []
  | .ne v1 v2 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        [encNotEqual ⟨v1, h.1⟩ ⟨v2, h.2⟩ (domOf S [⟨v1, h.1⟩, ⟨v2, h.2⟩])]
      else []
  | .eq_const v c =>
      if h : v < S.nInt then [encEqConst ⟨v, h⟩ c] else []
  | .ne_const v c =>
      if h : v < S.nInt then [encNeConst ⟨v, h⟩ c] else []
  | .at_most_k vars k =>
      if _ : ∀ v ∈ vars, v < S.nInt then [encAtMostK (toFinList S vars) (k : Int)] else []
  | .at_least_k vars k =>
      if _ : ∀ v ∈ vars, v < S.nInt then [encAtLeastK (toFinList S vars) (k : Int)] else []
  | .linear vars coeffs op target =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        encodeRel S op (coeffs.zip (toFinList S vars)) target
      else []
  | .sum vars op target =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        encodeRel S op ((toFinList S vars).map (fun v => ((1 : Int), v))) target
      else []
  | .schur_triple v1 v2 v3 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt ∧ v3 < S.nInt then
        [encNotAllEqualMulti [⟨v1, h.1⟩, ⟨v2, h.2.1⟩, ⟨v3, h.2.2⟩]
          (domOf S [⟨v1, h.1⟩, ⟨v2, h.2.1⟩, ⟨v3, h.2.2⟩])]
      else []
  -- Binary comparisons `v1 (op) v2`, encoded as `v1 − v2 (op) 0`.
  | .eq v1 v2 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        encodeRel S .EQ [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] 0 else []
  | .lt v1 v2 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        encodeRel S .LT [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] 0 else []
  | .le v1 v2 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        encodeRel S .LE [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] 0 else []
  | .gt v1 v2 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        encodeRel S .GT [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] 0 else []
  | .ge v1 v2 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        encodeRel S .GE [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] 0 else []
  -- `iff` is value-equality over the {0,1}-or-wider domain; same as `eq`.
  | .iff v1 v2 =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        encodeRel S .EQ [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] 0 else []
  -- `implies p q` is `q ≥ p` (Boolean order), encoded as `q − p ≥ 0`.
  | .implies p q =>
      if h : p < S.nInt ∧ q < S.nInt then
        encodeRel S .GE [((1 : Int), ⟨q, h.2⟩), ((-1 : Int), ⟨p, h.1⟩)] 0 else []
  -- Unary comparisons `v (op) c`.
  | .lt_const v c =>
      if h : v < S.nInt then encodeRel S .LT [((1 : Int), ⟨v, h⟩)] c else []
  | .le_const v c =>
      if h : v < S.nInt then encodeRel S .LE [((1 : Int), ⟨v, h⟩)] c else []
  | .gt_const v c =>
      if h : v < S.nInt then encodeRel S .GT [((1 : Int), ⟨v, h⟩)] c else []
  | .ge_const v c =>
      if h : v < S.nInt then encodeRel S .GE [((1 : Int), ⟨v, h⟩)] c else []
  -- `exactly_k`: unit-coefficient sum `= k`.
  | .exactly_k vars k =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        encodeRel S .EQ ((toFinList S vars).map (fun v => ((1 : Int), v))) (k : Int) else []
  -- Variable-target arithmetic: move the target variable to the LHS with coeff `−1`.
  | .sum_rel_var vars op tvar =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ tvar < S.nInt then
        encodeRel S op
          ((toFinList S vars).map (fun v => ((1 : Int), v)) ++ [((-1 : Int), ⟨tvar, h.2⟩)]) 0
      else []
  | .linear_rel_var vars coeffs op tvar =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ tvar < S.nInt then
        encodeRel S op (coeffs.zip (toFinList S vars) ++ [((-1 : Int), ⟨tvar, h.2⟩)]) 0
      else []
  -- Value (colour) precedence.  Its full Law–Lee semantics (`patternHolds`) implies the
  -- *staircase* relaxation `x_j ≤ j` (a positive colour `v` needs a strictly-earlier chain
  -- `v-1, …, 0`, so at most `j+1` distinct colours precede position `j`).  We emit exactly
  -- that staircase — every bit of pruning is sound (`value_precedence_staircase`), aux-free,
  -- and uses the existing unary `≤` encoder.
  | .value_precedence _colors =>
      (List.finRange S.nInt).flatMap (fun j => encodeRel S .LE [((1 : Int), j)] (j.val : Int))
  -- Constructors not yet in the PB fragment (wired in later milestones, or genuinely
  -- non-linear).  Each encodes to `[]` — sound, since dropping a constraint only weakens
  -- the PB formula.  Listed explicitly (no wildcard) so each `encodePattern` equation lemma
  -- is direct, keeping the soundness proofs' `simp only [encodePattern]` cheap.
  | .alldifferentOffset _ _ => []
  | .increasing _ => []
  | .count _ _ _ => []
  | .count_var _ _ _ => []
  | .element _ _ _ => []
  | .maximum _ _ => []
  | .minimum _ _ => []
  | .bound _ _ _ => []
  | .abs_diff_rel _ _ _ _ => []
  | .abs_diff_var _ _ _ => []
  | .modulo _ _ _ => []
  | .sliding_sum _ _ _ _ => []
  | .not_gate _ _ => []
  | .and_gate _ _ _ => []
  | .or_gate _ _ _ => []
  | .xor_gate _ _ _ => []
  | .nand_gate _ _ _ => []
  | .nor_gate _ _ _ => []
  | .and_all _ _ => []
  | .or_all _ _ => []
  | .xor_all _ _ => []
  | .if_then _ _ _ _ => []
  | .if_then_or _ _ _ _ => []
  | .product_rel_var _ _ _ => []
  | .strictLexRevLeader => []   -- aux-free dispatcher; the real (aux-using) encoding lives in `encodePatternAt`
  | .disjunctive _ _ => []
  | .unknown _ _ => []

/-- **Value precedence ⇒ staircase.**  If every positive colour at position `j` has its
    predecessor strictly earlier, then `a j ≤ j` for all `j` (chain `a j, a j − 1, …, 0`
    occupies `a j + 1 ≤ j + 1` distinct positions `≤ j`).  This is what makes the staircase
    PB encoding of `value_precedence` sound. -/
theorem value_precedence_staircase {m : ℕ} (a : Fin m → Int)
    (h : ∀ j : Fin m, 1 ≤ a j → ∃ i : Fin m, i.val < j.val ∧ a i = a j - 1) :
    ∀ j : Fin m, a j ≤ (j.val : Int) := by
  intro j
  have key : ∀ p : ℕ, ∀ j : Fin m, j.val < p → a j ≤ (j.val : Int) := by
    intro p
    induction p with
    | zero => intro j hj; omega
    | succ p ih =>
      intro j hj
      by_cases hpos : 1 ≤ a j
      · obtain ⟨i, hij, hai⟩ := h j hpos
        have hi : a i ≤ (i.val : Int) := ih i (by omega)
        omega
      · omega
  exact key (j.val + 1) j (by omega)

/-- Every entry `encodePattern` emits is aux-free. -/
theorem encodePattern_setsAux (c : IntConstraint S.nInt) (a : Fin S.nInt → Int)
    (e : EncConstr S) (he : e ∈ encodePattern S c) : e.setsAux a = [] := by
  cases c
  case alldifferent vars =>
    simp only [encodePattern] at he; split at he <;> simp_all [encAllDifferent]
  case ne v1 v2 =>
    simp only [encodePattern] at he; split at he <;> simp_all [encNotEqual]
  case eq_const v c =>
    simp only [encodePattern] at he; split at he <;> simp_all [encEqConst]
  case ne_const v c =>
    simp only [encodePattern] at he; split at he <;> simp_all [encNeConst]
  case at_most_k vars k =>
    simp only [encodePattern] at he; split at he <;> simp_all [encAtMostK]
  case at_least_k vars k =>
    simp only [encodePattern] at he; split at he <;> simp_all [encAtLeastK]
  case linear vars coeffs op target =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case sum vars op target =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case schur_triple v1 v2 v3 =>
    simp only [encodePattern] at he; split at he
    · rw [List.mem_singleton] at he; subst he; simp [encNotAllEqualMulti]
    · exact absurd he (by simp)
  case eq v1 v2 =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case lt v1 v2 =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case le v1 v2 =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case gt v1 v2 =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case ge v1 v2 =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case iff v1 v2 =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case implies p q =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case lt_const v c =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case le_const v c =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case gt_const v c =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case ge_const v c =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case exactly_k vars k =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case sum_rel_var vars op tvar =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case linear_rel_var vars coeffs op tvar =>
    simp only [encodePattern] at he; split at he
    · exact encodeRel_setsAux _ _ _ a e he
    · exact absurd he (by simp)
  case value_precedence colors =>
    simp only [encodePattern, List.mem_flatMap] at he
    obtain ⟨j, _, he⟩ := he
    exact encodeRel_setsAux _ _ _ a e he
  all_goals (simp only [encodePattern] at he; exact absurd he (by simp))

/-- **Generic per-constraint soundness.**  Each emitted entry's precondition follows from
    `patternHolds c a` — the single bridge that replaces every per-instance `*_sat` lemma. -/
theorem encodePattern_sound (c : IntConstraint S.nInt) (a : Fin S.nInt → Int)
    (hpat : patternHolds c a) (e : EncConstr S) (he : e ∈ encodePattern S c) : e.pre a := by
  cases c
  case alldifferent vars =>
      simp only [encodePattern] at he
      split at he
      · rename_i hwf
        rw [List.mem_singleton] at he; subst he
        show ((toFinList S vars).map a).Nodup
        rw [toFinList_map a vars hwf]; exact hpat
      · exact absurd he (by simp)
  case ne v1 v2 =>
      simp only [encodePattern] at he
      split at he
      · rename_i h
        rw [List.mem_singleton] at he; subst he
        show a ⟨v1, h.1⟩ ≠ a ⟨v2, h.2⟩
        have hh : valAt a v1 ≠ valAt a v2 := hpat
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case eq_const v c =>
      simp only [encodePattern] at he
      split at he
      · rename_i h
        rw [List.mem_singleton] at he; subst he
        show a ⟨v, h⟩ = c
        have hh : valAt a v = c := hpat
        simpa only [valAt, h, dite_true] using hh
      · exact absurd he (by simp)
  case ne_const v c =>
      simp only [encodePattern] at he
      split at he
      · rename_i h
        rw [List.mem_singleton] at he; subst he
        show a ⟨v, h⟩ ≠ c
        have hh : valAt a v ≠ c := hpat
        simpa only [valAt, h, dite_true] using hh
      · exact absurd he (by simp)
  case at_most_k vars k =>
      simp only [encodePattern] at he
      split at he
      · rename_i hwf
        rw [List.mem_singleton] at he; subst he
        show ((toFinList S vars).map a).sum ≤ (k : Int)
        rw [toFinList_map a vars hwf]; exact hpat
      · exact absurd he (by simp)
  case at_least_k vars k =>
      simp only [encodePattern] at he
      split at he
      · rename_i hwf
        rw [List.mem_singleton] at he; subst he
        show (k : Int) ≤ ((toFinList S vars).map a).sum
        rw [toFinList_map a vars hwf]; exact hpat
      · exact absurd he (by simp)
  case linear vars coeffs op target =>
      simp only [encodePattern] at he
      split at he
      · rename_i hwf
        refine encodeRel_sound op (coeffs.zip (toFinList S vars)) target a ?_ e he
        rw [linTerms_sum a coeffs vars hwf]; exact hpat
      · exact absurd he (by simp)
  case sum vars op target =>
      simp only [encodePattern] at he
      split at he
      · rename_i hwf
        refine encodeRel_sound op ((toFinList S vars).map (fun v => ((1 : Int), v))) target a ?_ e he
        rw [unitTerms_sum a vars hwf]; exact hpat
      · exact absurd he (by simp)
  case schur_triple v1 v2 v3 =>
      simp only [encodePattern] at he
      split at he
      · rename_i h
        rw [List.mem_singleton] at he; subst he
        have hp : a ⟨v1, h.1⟩ ≠ a ⟨v2, h.2.1⟩ ∨ a ⟨v1, h.1⟩ ≠ a ⟨v3, h.2.2⟩ ∨
            a ⟨v2, h.2.1⟩ ≠ a ⟨v3, h.2.2⟩ := by
          simpa only [patternHolds, valAt, h.1, h.2.1, h.2.2, dite_true] using hpat
        show ∃ i ∈ [(⟨v1, h.1⟩ : Fin S.nInt), ⟨v2, h.2.1⟩, ⟨v3, h.2.2⟩],
          ∃ i' ∈ [(⟨v1, h.1⟩ : Fin S.nInt), ⟨v2, h.2.1⟩, ⟨v3, h.2.2⟩], a i ≠ a i'
        rcases hp with hp | hp | hp
        · exact ⟨_, by simp, _, by simp, hp⟩
        · exact ⟨_, by simp, _, by simp, hp⟩
        · exact ⟨_, by simp, _, by simp, hp⟩
      · exact absurd he (by simp)
  case eq v1 v2 =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_bin_sound .EQ ⟨v1, h.1⟩ ⟨v2, h.2⟩ a ?_ e he
        have hh : valAt a v1 = valAt a v2 := hpat
        show a ⟨v1, h.1⟩ = a ⟨v2, h.2⟩
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case lt v1 v2 =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_bin_sound .LT ⟨v1, h.1⟩ ⟨v2, h.2⟩ a ?_ e he
        have hh : valAt a v1 < valAt a v2 := hpat
        show a ⟨v1, h.1⟩ < a ⟨v2, h.2⟩
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case le v1 v2 =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_bin_sound .LE ⟨v1, h.1⟩ ⟨v2, h.2⟩ a ?_ e he
        have hh : valAt a v1 ≤ valAt a v2 := hpat
        show a ⟨v1, h.1⟩ ≤ a ⟨v2, h.2⟩
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case gt v1 v2 =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_bin_sound .GT ⟨v1, h.1⟩ ⟨v2, h.2⟩ a ?_ e he
        have hh : valAt a v1 > valAt a v2 := hpat
        show a ⟨v1, h.1⟩ > a ⟨v2, h.2⟩
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case ge v1 v2 =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_bin_sound .GE ⟨v1, h.1⟩ ⟨v2, h.2⟩ a ?_ e he
        have hh : valAt a v1 ≥ valAt a v2 := hpat
        show a ⟨v1, h.1⟩ ≥ a ⟨v2, h.2⟩
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case iff v1 v2 =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_bin_sound .EQ ⟨v1, h.1⟩ ⟨v2, h.2⟩ a ?_ e he
        have hh : valAt a v1 = valAt a v2 := hpat
        show a ⟨v1, h.1⟩ = a ⟨v2, h.2⟩
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case implies p q =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_bin_sound .GE ⟨q, h.2⟩ ⟨p, h.1⟩ a ?_ e he
        have hh : valAt a q ≥ valAt a p := hpat
        show a ⟨q, h.2⟩ ≥ a ⟨p, h.1⟩
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case lt_const v c =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_unary_sound .LT ⟨v, h⟩ c a ?_ e he
        have hh : valAt a v < c := hpat
        show a ⟨v, h⟩ < c
        simpa only [valAt, h, dite_true] using hh
      · exact absurd he (by simp)
  case le_const v c =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_unary_sound .LE ⟨v, h⟩ c a ?_ e he
        have hh : valAt a v ≤ c := hpat
        show a ⟨v, h⟩ ≤ c
        simpa only [valAt, h, dite_true] using hh
      · exact absurd he (by simp)
  case gt_const v c =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_unary_sound .GT ⟨v, h⟩ c a ?_ e he
        have hh : valAt a v > c := hpat
        show a ⟨v, h⟩ > c
        simpa only [valAt, h, dite_true] using hh
      · exact absurd he (by simp)
  case ge_const v c =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_unary_sound .GE ⟨v, h⟩ c a ?_ e he
        have hh : valAt a v ≥ c := hpat
        show a ⟨v, h⟩ ≥ c
        simpa only [valAt, h, dite_true] using hh
      · exact absurd he (by simp)
  case exactly_k vars k =>
      simp only [encodePattern] at he; split at he
      · rename_i hwf
        refine encodeRel_sound .EQ ((toFinList S vars).map (fun v => ((1 : Int), v)))
          (k : Int) a ?_ e he
        rw [unitTerms_sum a vars hwf]
        show (vars.map (valAt a)).sum = (k : Int)
        exact hpat
      · exact absurd he (by simp)
  case sum_rel_var vars op tvar =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_var_sound op ((toFinList S vars).map (fun v => ((1 : Int), v)))
          ⟨tvar, h.2⟩ a ((vars.map (valAt a)).sum) (unitTerms_sum a vars h.1) ?_ e he
        have hh : relHolds op ((vars.map (valAt a)).sum) (valAt a tvar) := hpat
        simpa only [valAt, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case linear_rel_var vars coeffs op tvar =>
      simp only [encodePattern] at he; split at he
      · rename_i h
        refine encodeRel_var_sound op (coeffs.zip (toFinList S vars)) ⟨tvar, h.2⟩ a
          (List.zipWith (· * ·) coeffs (vars.map (valAt a))).sum
          (linTerms_sum a coeffs vars h.1) ?_ e he
        have hh : relHolds op
          (List.zipWith (· * ·) coeffs (vars.map (valAt a))).sum (valAt a tvar) := hpat
        simpa only [valAt, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case value_precedence colors =>
      simp only [encodePattern, List.mem_flatMap] at he
      obtain ⟨j, _, he⟩ := he
      have hp : ∀ j : Fin S.nInt, 1 ≤ a j → ∃ i : Fin S.nInt, i.val < j.val ∧ a i = a j - 1 :=
        hpat
      refine encodeRel_unary_sound .LE j (j.val : Int) a ?_ e he
      show a j ≤ (j.val : Int)
      exact value_precedence_staircase a hp j
  all_goals (simp only [encodePattern] at he; exact absurd he (by simp))

/-! ### Boolean-gate fold bounds (over `{0,1}`)

`and_all`/`or_all` reduce to the running `min`/`max` fold of `patternHolds`.  These pure-ℤ
lemmas give the linear bounds the PB encoding emits: `min ≤ each ≤ … ≥ Σ−(n−1)` and dually
`max ≥ each ≥ … ≤ Σ`. -/

/-- The running-min fold is `≤` its seed. -/
theorem foldl_minif_le_init (l : List ℤ) (init : ℤ) :
    l.foldl (fun acc x => if x < acc then x else acc) init ≤ init := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih => simp only [List.foldl_cons]; exact le_trans (ih _) (by split_ifs <;> omega)

/-- The running-min fold is `≤` every element. -/
theorem foldl_minif_le_mem (l : List ℤ) (init x : ℤ) (hx : x ∈ l) :
    l.foldl (fun acc x => if x < acc then x else acc) init ≤ x := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_trans (foldl_minif_le_init ys _) (by split_ifs <;> omega)
    · exact ih _ hmem

/-- Over `{0,1}`, the running-min fold is `≥ seed + Σ − length` (the AND lower bound). -/
theorem foldl_minif_ge_sum (l : List ℤ) (init : ℤ)
    (hinit : 0 ≤ init ∧ init ≤ 1) (hl : ∀ x ∈ l, 0 ≤ x ∧ x ≤ 1) :
    init + l.sum - (l.length : ℤ) ≤ l.foldl (fun acc x => if x < acc then x else acc) init := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.sum_cons, List.length_cons]
    have hy := hl y (by simp)
    have hmin01 : 0 ≤ (if y < init then y else init) ∧ (if y < init then y else init) ≤ 1 := by
      split_ifs <;> omega
    refine le_trans ?_ (ih (if y < init then y else init) hmin01 (fun x hx => hl x (by simp [hx])))
    split_ifs <;> push_cast <;> omega

/-- The running-max fold is `≥` its seed. -/
theorem foldl_maxif_ge_init (l : List ℤ) (init : ℤ) :
    init ≤ l.foldl (fun acc x => if x > acc then x else acc) init := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih => simp only [List.foldl_cons]; exact le_trans (by split_ifs <;> omega) (ih _)

/-- The running-max fold is `≥` every element. -/
theorem foldl_maxif_ge_mem (l : List ℤ) (init x : ℤ) (hx : x ∈ l) :
    x ≤ l.foldl (fun acc x => if x > acc then x else acc) init := by
  induction l generalizing init with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact le_trans (by split_ifs <;> omega) (foldl_maxif_ge_init ys _)
    · exact ih _ hmem

/-- Over `{0,1}` (here only `0 ≤ ·` is needed), the running-max fold is `≤ seed + Σ`
    (the OR upper bound). -/
theorem foldl_maxif_le_sum (l : List ℤ) (init : ℤ)
    (hinit : 0 ≤ init) (hl : ∀ x ∈ l, 0 ≤ x) :
    l.foldl (fun acc x => if x > acc then x else acc) init ≤ init + l.sum := by
  induction l generalizing init with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons, List.sum_cons]
    have hy := hl y (by simp)
    have hmax0 : 0 ≤ (if y > init then y else init) := by split_ifs <;> omega
    refine le_trans (ih (if y > init then y else init) hmax0 (fun x hx => hl x (by simp [hx]))) ?_
    split_ifs <;> omega

/-- An in-range index of `vars` lies in its `toFinList`. -/
theorem mem_toFinList {vars : List ℕ} {v : ℕ} (hv : v < S.nInt) (hmem : v ∈ vars) :
    (⟨v, hv⟩ : Fin S.nInt) ∈ toFinList S vars := by
  unfold toFinList
  exact List.mem_filterMap.mpr ⟨v, hmem, by rw [dif_pos hv]⟩

/-- On in-range indices, `toFinList` is value-faithful: mapping `Fin.val` back recovers
    the original `ℕ` list. -/
theorem toFinList_val (vars : List ℕ) (hwf : ∀ v ∈ vars, v < S.nInt) :
    (toFinList S vars).map Fin.val = vars := by
  unfold toFinList
  induction vars with
  | nil => simp
  | cons x xs ih =>
    have hx : x < S.nInt := hwf x (by simp)
    have ih' := ih (fun v hv => hwf v (by simp [hv]))
    simp only [List.filterMap_cons, hx, dite_true, List.map_cons, ih']

/-! ### Offset all-different: the pairwise Big-M expansion

`alldifferentOffset vars offsets` (`(vars.zip offsets).map (vᵢ + oᵢ)` pairwise distinct —
the N-Queens diagonals) decomposes into one Big-M disequality per pair:
`vᵢ + oᵢ ≠ vⱼ + oⱼ ⟺ vᵢ − vⱼ ≠ oⱼ − oᵢ`, each owning one selector from a contiguous
block threaded from `base`. -/

/-- Pair the head `(v, o)` against each later entry, selectors `base, base+1, …`. -/
def encodeOffsetHead (S : CSPSig) (v : Fin S.nInt) (o : ℤ) :
    List (Fin S.nInt × ℤ) → ℕ → List (EncConstr S)
  | [], _ => []
  | (w, p) :: rest, base =>
      encodeRelAt S base .NE [((1 : Int), v), ((-1 : Int), w)] (p - o)
        ++ encodeOffsetHead S v o rest (base + 1)

/-- All pairs of the zipped (variable, offset) list, selector blocks threaded. -/
def encodeOffsetPairs (S : CSPSig) : List (Fin S.nInt × ℤ) → ℕ → List (EncConstr S)
  | [], _ => []
  | (v, o) :: rest, base =>
      encodeOffsetHead S v o rest base ++ encodeOffsetPairs S rest (base + rest.length)

/-- Soundness of the head expansion: if the head's shifted value differs from every later
    entry's, every emitted Big-M precondition holds. -/
theorem encodeOffsetHead_sound (v : Fin S.nInt) (o : ℤ) (l : List (Fin S.nInt × ℤ))
    (base : ℕ) (a : Fin S.nInt → Int)
    (hne : ∀ q ∈ l, a v + o ≠ a q.1 + q.2) :
    ∀ e ∈ encodeOffsetHead S v o l base, e.pre a := by
  induction l generalizing base with
  | nil => intro e he; simp [encodeOffsetHead] at he
  | cons hd rest ih =>
    obtain ⟨w, p⟩ := hd
    intro e he
    simp only [encodeOffsetHead, List.mem_append] at he
    rcases he with he | he
    · refine encodeRelAt_sound base .NE [((1 : Int), v), ((-1 : Int), w)] (p - o) a ?_ e he
      have h1 : a v + o ≠ a w + p := hne (w, p) (by simp)
      rw [binTerms_sum]
      show a v - a w ≠ p - o
      omega
    · exact ih (base + 1) (fun q hq => hne q (by simp [hq])) e he

/-- Soundness of the pairwise expansion: pairwise-distinct shifted values give every
    emitted Big-M precondition. -/
theorem encodeOffsetPairs_sound (l : List (Fin S.nInt × ℤ)) (base : ℕ)
    (a : Fin S.nInt → Int)
    (hpw : List.Pairwise (fun p q => a p.1 + p.2 ≠ a q.1 + q.2) l) :
    ∀ e ∈ encodeOffsetPairs S l base, e.pre a := by
  induction l generalizing base with
  | nil => intro e he; simp [encodeOffsetPairs] at he
  | cons hd rest ih =>
    obtain ⟨v, o⟩ := hd
    rw [List.pairwise_cons] at hpw
    intro e he
    simp only [encodeOffsetPairs, List.mem_append] at he
    rcases he with he | he
    · exact encodeOffsetHead_sound v o rest base a (fun q hq => hpw.1 q hq) e he
    · exact ih (base + rest.length) hpw.2 e he

/-! ### `increasing`: the consecutive `≤` chain (aux-free) -/

/-- One `≤` per consecutive pair (implied by, and over a total order equivalent to, the
    pairwise order of `increasing`). -/
def encodeIncreasing (S : CSPSig) : List (Fin S.nInt) → List (EncConstr S)
  | x :: y :: rest =>
      encLinearLe [((1 : Int), x), ((-1 : Int), y)] 0 :: encodeIncreasing S (y :: rest)
  | _ => []

/-- The chain is aux-free. -/
theorem encodeIncreasing_setsAux (l : List (Fin S.nInt)) (a : Fin S.nInt → Int) :
    ∀ e ∈ encodeIncreasing S l, e.setsAux a = [] := by
  induction l with
  | nil => simp [encodeIncreasing]
  | cons x rest ih =>
    cases rest with
    | nil => simp [encodeIncreasing]
    | cons y rest' =>
      intro e he
      simp only [encodeIncreasing, List.mem_cons] at he
      rcases he with rfl | he
      · rfl
      · exact ih e he

/-- Soundness of the chain: pairwise-ordered values give every consecutive bound. -/
theorem encodeIncreasing_sound (l : List (Fin S.nInt)) (a : Fin S.nInt → Int)
    (hpw : List.Pairwise (· ≤ ·) (l.map a)) :
    ∀ e ∈ encodeIncreasing S l, e.pre a := by
  induction l with
  | nil => intro e he; simp [encodeIncreasing] at he
  | cons x rest ih =>
    cases rest with
    | nil => intro e he; simp [encodeIncreasing] at he
    | cons y rest' =>
      simp only [List.map_cons, List.pairwise_cons] at hpw
      intro e he
      simp only [encodeIncreasing, List.mem_cons] at he
      rcases he with rfl | he
      · show ([((1 : Int), x), ((-1 : Int), y)].map (fun p => p.1 * a p.2)).sum ≤ 0
        have hxy : a x ≤ a y := hpw.1 (a y) (by simp)
        rw [binTerms_sum]
        omega
      · refine ih ?_ e he
        simp only [List.map_cons, List.pairwise_cons]
        exact hpw.2

/-- Linear facets of a binary AND (`r = min x y`) over `{0,1}` inputs. -/
theorem and2_bounds (x y r : ℤ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (h : r = min x y) : r ≤ x ∧ r ≤ y ∧ x + y - r ≤ 1 := by
  rcases min_choice x y with hm | hm <;> rw [hm] at h <;>
    rcases le_total x y with hxy | hxy <;>
    simp only [min_eq_left, min_eq_right, hxy] at hm <;> omega

/-- Linear facets of a binary OR (`r = max x y`) over `{0,1}` inputs. -/
theorem or2_bounds (x y r : ℤ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1)
    (h : r = max x y) : x ≤ r ∧ y ≤ r ∧ r - x - y ≤ 0 := by
  rcases max_choice x y with hm | hm <;> rw [hm] at h <;>
    rcases le_total x y with hxy | hxy <;>
    simp only [max_eq_left, max_eq_right, hxy] at hm <;> omega

/-- Negating each summand negates the sum. -/
theorem sum_map_neg (l : List ℤ) : (l.map (fun x => -x)).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The `−1`-coefficient term list of `toFinList vars` sums to minus the plain value sum. -/
theorem negUnitTerms_sum (a : Fin S.nInt → Int) (vars : List ℕ)
    (hwf : ∀ v ∈ vars, v < S.nInt) :
    (((toFinList S vars).map (fun v => ((-1 : Int), v))).map (fun p => p.1 * a p.2)).sum
      = -(vars.map (valAt a)).sum := by
  have h1 : ((toFinList S vars).map (fun v => ((-1 : Int), v))).map (fun p => p.1 * a p.2)
      = ((toFinList S vars).map a).map (fun x => -x) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left (fun v _ => by simp)
  rw [h1, toFinList_map a vars hwf, sum_map_neg]

/-- The running-min fold over a `{0,1}` list, seeded by its own head, is bounded below by
    each element and above by `sum − (length − 1)` — the multi-input AND facets. -/
theorem andAll_bounds (m : ℤ) (ms : List ℤ) (r : ℤ)
    (h01 : ∀ y ∈ m :: ms, 0 ≤ y ∧ y ≤ 1)
    (hr : r = (m :: ms).foldl (fun acc x => if x < acc then x else acc) m) :
    (∀ y ∈ m :: ms, r ≤ y) ∧ (m :: ms).sum - (ms.length : ℤ) ≤ r := by
  have hstep : (m :: ms).foldl (fun acc x => if x < acc then x else acc) m
      = ms.foldl (fun acc x => if x < acc then x else acc) m := by
    rw [List.foldl_cons, if_neg (lt_irrefl m)]
  rw [hstep] at hr
  constructor
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hr]; exact foldl_minif_le_init ms y
    · rw [hr]; exact foldl_minif_le_mem ms m y hy
  · have hlow := foldl_minif_ge_sum ms m (h01 m (by simp))
      (fun x hx => h01 x (by simp [hx]))
    rw [hr]; simp only [List.sum_cons]; omega

/-- The running-max fold over a nonnegative list, seeded by its own head, is bounded above
    by each element's contribution and below by each element — the multi-input OR facets. -/
theorem orAll_bounds (m : ℤ) (ms : List ℤ) (r : ℤ)
    (h0 : ∀ y ∈ m :: ms, 0 ≤ y)
    (hr : r = (m :: ms).foldl (fun acc x => if x > acc then x else acc) m) :
    (∀ y ∈ m :: ms, y ≤ r) ∧ r ≤ (m :: ms).sum := by
  have hstep : (m :: ms).foldl (fun acc x => if x > acc then x else acc) m
      = ms.foldl (fun acc x => if x > acc then x else acc) m := by
    rw [List.foldl_cons, if_neg (lt_irrefl m)]
  rw [hstep] at hr
  constructor
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [hr]; exact foldl_maxif_ge_init ms y
    · rw [hr]; exact foldl_maxif_ge_mem ms m y hy
  · have hup := foldl_maxif_le_sum ms m (h0 m (by simp)) (fun x hx => h0 x (by simp [hx]))
    rw [hr]; simp only [List.sum_cons]; omega

/-! ### `if_then` / `if_then_or`: indicator implications (aux-free, exact)

`(v = value) → (nv = nvalue)` over the order encoding is the single linear constraint
`[v = value] ≤ [nv = nvalue]` on the equality indicators (`adContrib`); the `_or` form
bounds the antecedent indicator by the *sum* of the allowed-value indicators. -/

/-- A sum of nonnegative integers is nonnegative. -/
theorem sum_nonneg_of_mem (l : List ℤ) (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons]
    have hx := h x (by simp)
    have := ih (fun y hy => h y (by simp [hy]))
    omega

/-- Each member of a nonnegative list is at most the sum. -/
theorem le_sum_of_mem (l : List ℤ) (h0 : ∀ x ∈ l, 0 ≤ x) {x : ℤ} (hx : x ∈ l) :
    x ≤ l.sum := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · have := sum_nonneg_of_mem ys (fun z hz => h0 z (by simp [hz]))
      omega
    · have hy := h0 y (by simp)
      have := ih (fun z hz => h0 z (by simp [hz])) hx'
      omega

/-- Negating every coefficient negates the signed sum. -/
theorem signedEval_negTerms {V : Type} (v : V → Bool) (ts : List (Int × Lit V)) :
    signedEval v (ts.map (fun p => (-p.1, p.2))) = -signedEval v ts := by
  simp only [signedEval, List.map_map]
  have h1 : ((fun p => p.1 * (evalLit v p.2 : Int)) ∘ fun p : Int × Lit V => (-p.1, p.2))
      = fun p : Int × Lit V => -(p.1 * (evalLit v p.2 : Int)) := by
    funext p; simp [neg_mul]
  rw [h1]
  have h2 : ts.map (fun p : Int × Lit V => -(p.1 * (evalLit v p.2 : Int)))
      = (ts.map (fun p => p.1 * (evalLit v p.2 : Int))).map (fun x => -x) := by
    rw [List.map_map]; rfl
  rw [h2, sum_map_neg]

/-- `[v = value] ≤ [nv = nvalue]` as a signed constraint (the implication's facet). -/
def encodeIfThen (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt) (nvalue : Int) :
    SignedPBConstr (PBVar S) where
  terms := (adContrib v value).1
    ++ (adContrib nv nvalue).1.map (fun p => (-p.1, p.2))
  rhs := (adContrib nv nvalue).2 - (adContrib v value).2

/-- Soundness: the disjunction `v ≠ value ∨ nv = nvalue` gives the implication facet. -/
theorem encodeIfThen_sound (val : Valuation S) (hv : val.orderConsistent)
    (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt) (nvalue : Int)
    (h : val.intValue v ≠ value ∨ val.intValue nv = nvalue) :
    (encodeIfThen v value nv nvalue).sat val := by
  have hA := adContrib_eval val hv v value
  have hB := adContrib_eval val hv nv nvalue
  simp only [SignedPBConstr.sat, encodeIfThen, signedEval_append, signedEval_negTerms]
  rcases h with h | h
  · rw [if_neg h] at hA
    by_cases hB' : val.intValue nv = nvalue
    · rw [if_pos hB'] at hB; linarith
    · rw [if_neg hB'] at hB; linarith
  · rw [if_pos h] at hB
    by_cases hA' : val.intValue v = value
    · rw [if_pos hA'] at hA; linarith
    · rw [if_neg hA'] at hA; linarith

/-- The allowed-value indicator sum of `if_then_or`'s consequent. -/
theorem signedEval_indSum (val : Valuation S) (hv : val.orderConsistent)
    (nv : Fin S.nInt) (allowed : List Int) :
    signedEval val
        (allowed.flatMap (fun d => (adContrib nv d).1.map (fun p => (-p.1, p.2))))
      = (allowed.map (fun d => if val.intValue nv = d then (1 : Int) else 0)).sum
        + (allowed.map (fun d => (adContrib nv d).2)).sum := by
  induction allowed with
  | nil => simp [signedEval]
  | cons d ds ih =>
    simp only [List.flatMap_cons, signedEval_append, List.map_cons, List.sum_cons]
    rw [ih, signedEval_negTerms]
    have h := adContrib_eval val hv nv d
    linarith

/-- `[v = value] ≤ Σ_{d ∈ allowed} [nv = d]` as a signed constraint. -/
def encodeIfThenOr (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt)
    (allowed : List Int) : SignedPBConstr (PBVar S) where
  terms := (adContrib v value).1
    ++ allowed.flatMap (fun d => (adContrib nv d).1.map (fun p => (-p.1, p.2)))
  rhs := (allowed.map (fun d => (adContrib nv d).2)).sum - (adContrib v value).2

/-- Soundness: `v ≠ value ∨ nv ∈ allowed` gives the indicator-sum facet. -/
theorem encodeIfThenOr_sound (val : Valuation S) (hv : val.orderConsistent)
    (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt) (allowed : List Int)
    (h : val.intValue v ≠ value ∨ val.intValue nv ∈ allowed) :
    (encodeIfThenOr v value nv allowed).sat val := by
  have hA := adContrib_eval val hv v value
  have hpos : (0 : Int)
      ≤ (allowed.map (fun d => if val.intValue nv = d then (1 : Int) else 0)).sum := by
    refine sum_nonneg_of_mem _ ?_
    intro x hx
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
    split <;> omega
  simp only [SignedPBConstr.sat, encodeIfThenOr, signedEval_append]
  rw [signedEval_indSum val hv nv allowed]
  rcases h with h | h
  · rw [if_neg h] at hA
    linarith
  · have hone : (1 : Int)
        ≤ (allowed.map (fun d => if val.intValue nv = d then (1 : Int) else 0)).sum := by
      have hmem : (if val.intValue nv = val.intValue nv then (1 : Int) else 0)
          ∈ allowed.map (fun d => if val.intValue nv = d then (1 : Int) else 0) :=
        List.mem_map.mpr ⟨val.intValue nv, h, rfl⟩
      rw [if_pos rfl] at hmem
      refine le_sum_of_mem _ ?_ hmem
      intro x hx
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
      split <;> omega
    by_cases hA' : val.intValue v = value
    · rw [if_pos hA'] at hA; linarith
    · rw [if_neg hA'] at hA; linarith

/-- **Bridge.** A normalized `encodeIfThen` is modelled by `extend` whenever the
    disjunction holds on the recovered values. -/
theorem extend_sat_encodeIfThen (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt) (nvalue : Int)
    (h : a v ≠ value ∨ a nv = nvalue)
    (c' : PBConstr (PBVar S)) (hc : normalize (encodeIfThen v value nv nvalue) = some c') :
    c'.sat (extend a bA auxA) := by
  rw [← normalize_sat_iff _ _ hc]
  refine encodeIfThen_sound _ (extend_orderConsistent a bA auxA) v value nv nvalue ?_
  rw [extend_intValue a bA auxA hdom v, extend_intValue a bA auxA hdom nv]
  exact h

/-- **Bridge.** A normalized `encodeIfThenOr` is modelled by `extend` whenever the
    disjunction holds on the recovered values. -/
theorem extend_sat_encodeIfThenOr (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt) (allowed : List Int)
    (h : a v ≠ value ∨ a nv ∈ allowed)
    (c' : PBConstr (PBVar S)) (hc : normalize (encodeIfThenOr v value nv allowed) = some c') :
    c'.sat (extend a bA auxA) := by
  rw [← normalize_sat_iff _ _ hc]
  refine encodeIfThenOr_sound _ (extend_orderConsistent a bA auxA) v value nv allowed ?_
  rw [extend_intValue a bA auxA hdom v, extend_intValue a bA auxA hdom nv]
  exact h

/-- `if_then` as a soundness-carrying entry (aux-free). -/
def encIfThen (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt) (nvalue : Int) :
    EncConstr S where
  constrs := (normalize (encodeIfThen v value nv nvalue)).toList
  pre := fun a => a v ≠ value ∨ a nv = nvalue
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hpre _ c hc
    rw [Option.mem_toList] at hc
    exact extend_sat_encodeIfThen a bA auxA hdom v value nv nvalue hpre c hc

/-- `if_then_or` as a soundness-carrying entry (aux-free). -/
def encIfThenOr (v : Fin S.nInt) (value : Int) (nv : Fin S.nInt) (allowed : List Int) :
    EncConstr S where
  constrs := (normalize (encodeIfThenOr v value nv allowed)).toList
  pre := fun a => a v ≠ value ∨ a nv ∈ allowed
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hpre _ c hc
    rw [Option.mem_toList] at hc
    exact extend_sat_encodeIfThenOr a bA auxA hdom v value nv allowed hpre c hc

/-! ### Gated linear disjunction: `Σ_A ≤ b_A ∨ Σ_B ≤ b_B` via one Big-M selector

The general two-branch disjunction of linear `≤`-constraints (the `abs_diff_*`
family's workhorse): the selector picks the enforced branch, Big-M relaxes the other. -/

/-- The gated pair: `s = false ⇒ Σ_A ≤ b_A`, `s = true ⇒ Σ_B ≤ b_B`. -/
def encodeOrLe (tA : List (Int × Fin S.nInt)) (bA : Int)
    (tB : List (Int × Fin S.nInt)) (bB : Int) (s : Fin S.nAux) :
    List (SignedPBConstr (PBVar S)) :=
  [ (encodeLinearLe tA bA).addTerm (bigM tA bA) (.pos (.aux s)),
    (encodeLinearLe tB (bB + bigM tB bB)).addTerm (-(bigM tB bB)) (.pos (.aux s)) ]

/-- **Soundness.**  If one branch holds and the selector is set to
    `decide ¬(branch A)`, both gated constraints hold. -/
theorem encodeOrLe_sound (v : Valuation S) (hv : v.orderConsistent)
    (tA : List (Int × Fin S.nInt)) (bA : Int)
    (tB : List (Int × Fin S.nInt)) (bB : Int) (s : Fin S.nAux)
    (hor : (tA.map (fun p => p.1 * v.intValue p.2)).sum ≤ bA
      ∨ (tB.map (fun p => p.1 * v.intValue p.2)).sum ≤ bB)
    (hs : v (.aux s) = decide (¬ (tA.map (fun p => p.1 * v.intValue p.2)).sum ≤ bA)) :
    ∀ c ∈ encodeOrLe tA bA tB bB s, c.sat v := by
  have hbA := linear_abs_bound v hv tA
  have hbB := linear_abs_bound v hv tB
  rw [abs_le] at hbA hbB
  have habsA : bA ≤ |bA| := le_abs_self bA
  have habsA' : -bA ≤ |bA| := neg_le_abs bA
  have habsB : bB ≤ |bB| := le_abs_self bB
  have habsB' : -bB ≤ |bB| := neg_le_abs bB
  have hsint : (evalLit v (.pos (.aux s)) : Int)
      = if (tA.map (fun p => p.1 * v.intValue p.2)).sum ≤ bA then 0 else 1 := by
    simp only [evalLit, hs]
    by_cases h : (tA.map (fun p => p.1 * v.intValue p.2)).sum ≤ bA <;> simp [h]
  intro c hc
  simp only [encodeOrLe, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · show signedEval v _ ≥ (encodeLinearLe tA bA).rhs
    rw [signedEval_addTerm, signedEval_encode_eq, hsint]
    simp only [encodeLinearLe, bigM]
    by_cases h : (tA.map (fun p => p.1 * v.intValue p.2)).sum ≤ bA
    · rw [if_pos h, mul_zero]
      omega
    · rw [if_neg h, mul_one]
      omega
  · show signedEval v _ ≥ (encodeLinearLe tB (bB + bigM tB bB)).rhs
    rw [signedEval_addTerm, signedEval_encode_eq, hsint]
    simp only [encodeLinearLe, bigM]
    by_cases h : (tA.map (fun p => p.1 * v.intValue p.2)).sum ≤ bA
    · rw [if_pos h, mul_zero]
      omega
    · rw [if_neg h, mul_one]
      have hB : (tB.map (fun p => p.1 * v.intValue p.2)).sum ≤ bB := by
        rcases hor with hA | hB
        · exact absurd hA h
        · exact hB
      omega

/-- The gated disjunction as a soundness-carrying entry (owns the selector `s`). -/
def encOrLe (tA : List (Int × Fin S.nInt)) (bA : Int)
    (tB : List (Int × Fin S.nInt)) (bB : Int) (s : Fin S.nAux) : EncConstr S where
  constrs := (encodeOrLe tA bA tB bB s).filterMap normalize
  pre := fun a => (tA.map (fun p => p.1 * a p.2)).sum ≤ bA
    ∨ (tB.map (fun p => p.1 * a p.2)).sum ≤ bB
  setsAux := fun a =>
    [(s, decide (¬ (tA.map (fun p => p.1 * a p.2)).sum ≤ bA))]
  sound := by
    intro a bA' auxA hdom hpre hframe c hc
    rw [List.mem_filterMap] at hc
    obtain ⟨sc, hsc, hnorm⟩ := hc
    rw [← normalize_sat_iff _ _ hnorm]
    have hsumA : (tA.map (fun p => p.1 * (extend a bA' auxA).intValue p.2)).sum
        = (tA.map (fun p => p.1 * a p.2)).sum :=
      congrArg List.sum (List.map_congr_left
        (fun p _ => by rw [extend_intValue a bA' auxA hdom p.2]))
    have hsumB : (tB.map (fun p => p.1 * (extend a bA' auxA).intValue p.2)).sum
        = (tB.map (fun p => p.1 * a p.2)).sum :=
      congrArg List.sum (List.map_congr_left
        (fun p _ => by rw [extend_intValue a bA' auxA hdom p.2]))
    refine encodeOrLe_sound (extend a bA' auxA)
      (extend_orderConsistent a bA' auxA) tA bA tB bB s ?_ ?_ sc hsc
    · rw [hsumA, hsumB]
      exact hpre
    · rw [extend_aux, hsumA]
      exact hframe (s, decide (¬ (tA.map (fun p => p.1 * a p.2)).sum ≤ bA)) (by simp)

/-! ### `element`: per-position implications (aux-free, exact)

`arr[idx − 1] = res` (1-based `idx`) decomposes into the index bounds
`1 ≤ idx ≤ |arr|` plus one `if_then` implication `[idx = p] → [res = arr[p−1]]` per
position. -/

/-- The per-position implications, positions counted from `p`. -/
def encodeElementCases (idx res : Fin S.nInt) : List ℤ → ℤ → List (EncConstr S)
  | [], _ => []
  | x :: rest, p => encIfThen idx p res x :: encodeElementCases idx res rest (p + 1)

/-- The per-position implications are aux-free. -/
theorem encodeElementCases_setsAux (idx res : Fin S.nInt) (arr : List ℤ) (p : ℤ)
    (a : Fin S.nInt → Int) :
    ∀ e ∈ encodeElementCases idx res arr p, e.setsAux a = [] := by
  induction arr generalizing p with
  | nil => simp [encodeElementCases]
  | cons x rest ih =>
    intro e he
    simp only [encodeElementCases, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact ih (p + 1) e he

/-- Soundness of the per-position implications from the lookup function. -/
theorem encodeElementCases_sound (idx res : Fin S.nInt) (arr : List ℤ) (p : ℤ)
    (a : Fin S.nInt → Int)
    (hLook : ∀ (q : ℕ) (y : ℤ), arr[q]? = some y → a idx = p + q → a res = y) :
    ∀ e ∈ encodeElementCases idx res arr p, e.pre a := by
  induction arr generalizing p with
  | nil => intro e he; simp [encodeElementCases] at he
  | cons x rest ih =>
    intro e he
    simp only [encodeElementCases, List.mem_cons] at he
    rcases he with rfl | he
    · show a idx ≠ p ∨ a res = x
      by_cases hp : a idx = p
      · right
        refine hLook 0 x (by simp) ?_
        rw [hp]
        simp
      · left
        exact hp
    · refine ih (p + 1) ?_ e he
      intro q y hq hidx
      refine hLook (q + 1) y (by simpa using hq) ?_
      rw [hidx]
      push_cast
      ring

/-! ### `count`: the indicator-sum equality (aux-free, exact)

`Σⱼ [xⱼ = value] = n`, as the `≥ n` and `≤ n` halves over the equality indicators. -/

/-- Variable-indexed indicator sum (negated `adContrib`s). -/
theorem signedEval_varIndSum (val : Valuation S) (hv : val.orderConsistent)
    (value : Int) (js : List (Fin S.nInt)) :
    signedEval val
        (js.flatMap (fun j => (adContrib j value).1.map (fun p => (-p.1, p.2))))
      = (js.map (fun j => if val.intValue j = value then (1 : Int) else 0)).sum
        + (js.map (fun j => (adContrib j value).2)).sum := by
  induction js with
  | nil => simp [signedEval]
  | cons j tl ih =>
    simp only [List.flatMap_cons, signedEval_append, List.map_cons, List.sum_cons]
    rw [ih, signedEval_negTerms]
    have h := adContrib_eval val hv j value
    linarith

/-- Variable-indexed indicator sum, unnegated (the `≤` half's terms). -/
theorem signedEval_varIndSumNeg (val : Valuation S) (hv : val.orderConsistent)
    (value : Int) (js : List (Fin S.nInt)) :
    signedEval val (js.flatMap (fun j => (adContrib j value).1))
      = -(js.map (fun j => if val.intValue j = value then (1 : Int) else 0)).sum
        - (js.map (fun j => (adContrib j value).2)).sum := by
  induction js with
  | nil => simp [signedEval]
  | cons j tl ih =>
    simp only [List.flatMap_cons, signedEval_append, List.map_cons, List.sum_cons]
    rw [ih]
    have h := adContrib_eval val hv j value
    linarith

/-- `Σⱼ [xⱼ = value] ≥ n`. -/
def encodeCountGe (js : List (Fin S.nInt)) (value : Int) (n : ℕ) :
    SignedPBConstr (PBVar S) where
  terms := js.flatMap (fun j => (adContrib j value).1.map (fun p => (-p.1, p.2)))
  rhs := (n : Int) + (js.map (fun j => (adContrib j value).2)).sum

/-- `Σⱼ [xⱼ = value] ≤ n`. -/
def encodeCountLe (js : List (Fin S.nInt)) (value : Int) (n : ℕ) :
    SignedPBConstr (PBVar S) where
  terms := js.flatMap (fun j => (adContrib j value).1)
  rhs := -(n : Int) - (js.map (fun j => (adContrib j value).2)).sum

/-- The indicator sum counts the filter length. -/
theorem sum_ite_eq_filter_length (l : List ℤ) (value : ℤ) :
    (l.map (fun y => if y = value then (1 : Int) else 0)).sum
      = ((l.filter (· = value)).length : Int) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x = value
    · simp only [List.map_cons, List.sum_cons, if_pos hx, List.filter_cons]
      rw [if_pos (by simpa using hx), List.length_cons, ih]
      push_cast
      ring
    · simp only [List.map_cons, List.sum_cons, if_neg hx, List.filter_cons]
      rw [if_neg (by simpa using hx)]
      rw [ih]
      omega

/-- Soundness of both halves from the exact indicator count. -/
theorem encodeCount_sound (val : Valuation S) (hv : val.orderConsistent)
    (js : List (Fin S.nInt)) (value : Int) (n : ℕ)
    (hsum : (js.map (fun j => if val.intValue j = value then (1 : Int) else 0)).sum
      = (n : Int)) :
    (encodeCountGe js value n).sat val ∧ (encodeCountLe js value n).sat val := by
  constructor
  · simp only [SignedPBConstr.sat, encodeCountGe]
    rw [signedEval_varIndSum val hv value js, hsum]
  · simp only [SignedPBConstr.sat, encodeCountLe]
    rw [signedEval_varIndSumNeg val hv value js, hsum]

/-! ### `count_var`: gated cardinality per domain value of the target (aux-free, exact)

For each `n'` in the count variable's domain: `[cvar = n'] → Σⱼ [xⱼ = value] = n'`,
as two indicator-gated halves (`Σ ≥ n'·indc` and `Σ ≤ n'·indc + |js|·(1 − indc)`). -/

/-- Scaling every coefficient scales the signed sum. -/
theorem signedEval_scaleTerms {V : Type} (v : V → Bool) (k : Int)
    (ts : List (Int × Lit V)) :
    signedEval v (ts.map (fun p => (k * p.1, p.2))) = k * signedEval v ts := by
  induction ts with
  | nil => simp [signedEval]
  | cons p tl ih =>
    simp only [signedEval, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

/-- An indicator sum is at most the list length. -/
theorem sum_ite_le_length (l : List ℤ) (value : ℤ) :
    (l.map (fun y => if y = value then (1 : Int) else 0)).sum ≤ (l.length : Int) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    split <;> push_cast <;> omega

/-- Gated lower half: `Σⱼ [xⱼ = value] ≥ n' · [cvar = n']`. -/
def encodeCountVarGe (js : List (Fin S.nInt)) (value : Int) (cvar : Fin S.nInt)
    (n' : Int) : SignedPBConstr (PBVar S) where
  terms := js.flatMap (fun j => (adContrib j value).1.map (fun p => (-p.1, p.2)))
    ++ (adContrib cvar n').1.map (fun p => (n' * p.1, p.2))
  rhs := (js.map (fun j => (adContrib j value).2)).sum - n' * (adContrib cvar n').2

/-- Gated upper half: `Σⱼ [xⱼ = value] ≤ n'·[cvar = n'] + |js|·(1 − [cvar = n'])`. -/
def encodeCountVarLe (js : List (Fin S.nInt)) (value : Int) (cvar : Fin S.nInt)
    (n' : Int) : SignedPBConstr (PBVar S) where
  terms := js.flatMap (fun j => (adContrib j value).1)
    ++ ((adContrib cvar n').1.map (fun p => (-p.1, p.2))).map
        (fun p => ((n' - (js.length : Int)) * p.1, p.2))
  rhs := -(js.length : Int) - (js.map (fun j => (adContrib j value).2)).sum
    + (n' - (js.length : Int)) * (adContrib cvar n').2

/-- Soundness of both gated halves from `Σ indicators = intValue cvar`. -/
theorem encodeCountVar_sound (val : Valuation S) (hv : val.orderConsistent)
    (js : List (Fin S.nInt)) (value : Int) (cvar : Fin S.nInt) (n' : Int)
    (hsum : (js.map (fun j => if val.intValue j = value then (1 : Int) else 0)).sum
      = val.intValue cvar) :
    (encodeCountVarGe js value cvar n').sat val
      ∧ (encodeCountVarLe js value cvar n').sat val := by
  have hC := adContrib_eval val hv cvar n'
  have hpos : (0 : Int)
      ≤ (js.map (fun j => if val.intValue j = value then (1 : Int) else 0)).sum := by
    refine sum_nonneg_of_mem _ ?_
    intro x hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
    split <;> omega
  have hlen : (js.map (fun j => if val.intValue j = value then (1 : Int) else 0)).sum
      ≤ (js.length : Int) := by
    have h1 : js.map (fun j => if val.intValue j = value then (1 : Int) else 0)
        = (js.map val.intValue).map (fun y => if y = value then (1 : Int) else 0) := by
      rw [List.map_map]; rfl
    have h2 := sum_ite_le_length (js.map val.intValue) value
    rw [List.length_map] at h2
    rw [h1]
    exact h2
  constructor
  · simp only [SignedPBConstr.sat, encodeCountVarGe, signedEval_append,
      signedEval_scaleTerms]
    rw [signedEval_varIndSum val hv value js]
    by_cases hc : val.intValue cvar = n'
    · rw [if_pos hc] at hC
      have hS : signedEval val (adContrib cvar n').1 = -1 - (adContrib cvar n').2 := by
        linarith
      rw [hsum, hc, hS]
      ring_nf
      exact le_refl _
    · rw [if_neg hc] at hC
      have hS : signedEval val (adContrib cvar n').1 = -(adContrib cvar n').2 := by
        linarith
      rw [hS]
      ring_nf
      nlinarith [hpos]
  · simp only [SignedPBConstr.sat, encodeCountVarLe, signedEval_append,
      signedEval_scaleTerms, signedEval_negTerms]
    rw [signedEval_varIndSumNeg val hv value js]
    by_cases hc : val.intValue cvar = n'
    · rw [if_pos hc] at hC
      have hS : signedEval val (adContrib cvar n').1 = -1 - (adContrib cvar n').2 := by
        linarith
      rw [hsum, hc, hS]
      ring_nf
      exact le_refl _
    · rw [if_neg hc] at hC
      have hS : signedEval val (adContrib cvar n').1 = -(adContrib cvar n').2 := by
        linarith
      rw [hS]
      ring_nf
      nlinarith [hlen]

/-- `count_var` as a soundness-carrying entry (aux-free): the gated pair for every value
    in the count variable's domain. -/
def encCountVar (js : List (Fin S.nInt)) (value : Int) (cvar : Fin S.nInt) :
    EncConstr S where
  constrs := (S.values cvar).flatMap (fun n' =>
    (normalize (encodeCountVarGe js value cvar n')).toList
      ++ (normalize (encodeCountVarLe js value cvar n')).toList)
  pre := fun a => ((((js.map a).filter (· = value)).length : Int)) = a cvar
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hpre _ c hc
    have hsum : (js.map (fun j =>
        if (extend a bA auxA).intValue j = value then (1 : Int) else 0)).sum
        = (extend a bA auxA).intValue cvar := by
      have hmap : js.map (fun j =>
          if (extend a bA auxA).intValue j = value then (1 : Int) else 0)
          = (js.map a).map (fun y => if y = value then (1 : Int) else 0) := by
        rw [List.map_map]
        refine List.map_congr_left (fun j _ => ?_)
        simp only [Function.comp_apply, extend_intValue a bA auxA hdom j]
      rw [hmap, sum_ite_eq_filter_length, extend_intValue a bA auxA hdom cvar, hpre]
    rw [List.mem_flatMap] at hc
    obtain ⟨n', _, hc⟩ := hc
    have hboth := encodeCountVar_sound (extend a bA auxA)
      (extend_orderConsistent a bA auxA) js value cvar n' hsum
    rw [List.mem_append] at hc
    rcases hc with hc | hc <;> rw [Option.mem_toList] at hc <;>
      rw [← normalize_sat_iff _ _ hc]
    · exact hboth.1
    · exact hboth.2

/-! ### `maximum` / `minimum` attainment (aux-free, exact)

For each domain value `d` of the target: `[mx = d] ≤ Σᵥ ⟦v ≥ d⟧` (resp.
`[mn = d] ≤ Σᵥ ⟦v ≤ d⟧`) — the consequent is a sum of single order-encoding
threshold literals, so no selectors are needed.  Combined with the per-element
bounds this pins the target to an attained extremum. -/

/-- A `{0,1}`-ite sum is nonnegative. -/
theorem sum_ite_pred_nonneg {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    0 ≤ (l.map (fun x => if p x then (1 : Int) else 0)).sum := by
  refine sum_nonneg_of_mem _ ?_
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  split <;> omega

/-- A `{0,1}`-ite sum is at most the length. -/
theorem sum_ite_pred_le_length {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map (fun x => if p x then (1 : Int) else 0)).sum ≤ (l.length : Int) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    split <;> push_cast <;> omega

/-- With one falsifying member, a `{0,1}`-ite sum is at most `length − 1`. -/
theorem sum_ite_pred_le_length_sub_one {α : Type} (l : List α) (p : α → Prop)
    [DecidablePred p] {x₀ : α} (hx₀ : x₀ ∈ l) (hnp : ¬ p x₀) :
    (l.map (fun x => if p x then (1 : Int) else 0)).sum ≤ (l.length : Int) - 1 := by
  induction l with
  | nil => simp at hx₀
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rcases List.mem_cons.mp hx₀ with rfl | hmem
    · rw [if_neg hnp]
      have := sum_ite_pred_le_length ys p
      push_cast
      omega
    · have := ih hmem
      split <;> push_cast <;> omega

/-- With one satisfying member, a `{0,1}`-ite sum is at least `1`. -/
theorem one_le_sum_ite_pred {α : Type} (l : List α) (p : α → Prop) [DecidablePred p]
    {x₀ : α} (hx₀ : x₀ ∈ l) (hp : p x₀) :
    (1 : Int) ≤ (l.map (fun x => if p x then (1 : Int) else 0)).sum := by
  have hmem : (if p x₀ then (1 : Int) else 0)
      ∈ l.map (fun x => if p x then (1 : Int) else 0) :=
    List.mem_map.mpr ⟨x₀, hx₀, rfl⟩
  rw [if_pos hp] at hmem
  refine le_sum_of_mem _ ?_ hmem
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  split <;> omega

/-- Threshold-literal sum `Σᵥ ⟦v ≤ d⟧` (coefficient `+1`). -/
theorem signedEval_thrLeSum (val : Valuation S) (hv : val.orderConsistent)
    (d : Int) (js : List (Fin S.nInt)) :
    signedEval val
        (js.flatMap (fun v => (litConstContrib (1 : Int) (LitConst.mkLeLit S v d)).1))
      = (js.map (fun v => if val.intValue v ≤ d then (1 : Int) else 0)).sum
        - (js.map (fun v =>
            (litConstContrib (1 : Int) (LitConst.mkLeLit S v d)).2)).sum := by
  induction js with
  | nil => simp [signedEval]
  | cons j tl ih =>
    simp only [List.flatMap_cons, signedEval_append, List.map_cons, List.sum_cons]
    rw [ih]
    have h := litConstContrib_eval val (1 : Int) (LitConst.mkLeLit S j d)
    rw [mkLeLit_eval val hv j d] at h
    by_cases hj : val.intValue j ≤ d
    · rw [if_pos hj] at h ⊢; linarith
    · rw [if_neg hj] at h ⊢; linarith

/-- Negated threshold-literal sum `−Σᵥ ⟦v ≤ d−1⟧` (the literal part of `Σᵥ ⟦v ≥ d⟧`). -/
theorem signedEval_thrGeSum (val : Valuation S) (hv : val.orderConsistent)
    (d : Int) (js : List (Fin S.nInt)) :
    signedEval val
        (js.flatMap (fun v =>
          (litConstContrib (-1 : Int) (LitConst.mkLeLit S v (d - 1))).1))
      = -(js.map (fun v => if val.intValue v ≤ d - 1 then (1 : Int) else 0)).sum
        - (js.map (fun v =>
            (litConstContrib (-1 : Int) (LitConst.mkLeLit S v (d - 1))).2)).sum := by
  induction js with
  | nil => simp [signedEval]
  | cons j tl ih =>
    simp only [List.flatMap_cons, signedEval_append, List.map_cons, List.sum_cons]
    rw [ih]
    have h := litConstContrib_eval val (-1 : Int) (LitConst.mkLeLit S j (d - 1))
    rw [mkLeLit_eval val hv j (d - 1)] at h
    by_cases hj : val.intValue j ≤ d - 1
    · rw [if_pos hj] at h ⊢; linarith
    · rw [if_neg hj] at h ⊢; linarith

/-- `[mx = d] ≤ Σᵥ ⟦v ≥ d⟧` as a signed constraint. -/
def encodeMaxAttainAt (js : List (Fin S.nInt)) (mx : Fin S.nInt) (d : Int) :
    SignedPBConstr (PBVar S) where
  terms := js.flatMap (fun v =>
      (litConstContrib (-1 : Int) (LitConst.mkLeLit S v (d - 1))).1)
    ++ (adContrib mx d).1
  rhs := -(js.length : Int)
    - (js.map (fun v =>
        (litConstContrib (-1 : Int) (LitConst.mkLeLit S v (d - 1))).2)).sum
    - (adContrib mx d).2

/-- `[mn = d] ≤ Σᵥ ⟦v ≤ d⟧` as a signed constraint. -/
def encodeMinAttainAt (js : List (Fin S.nInt)) (mn : Fin S.nInt) (d : Int) :
    SignedPBConstr (PBVar S) where
  terms := js.flatMap (fun v => (litConstContrib (1 : Int) (LitConst.mkLeLit S v d)).1)
    ++ (adContrib mn d).1
  rhs := -(js.map (fun v =>
      (litConstContrib (1 : Int) (LitConst.mkLeLit S v d)).2)).sum
    - (adContrib mn d).2

/-- Soundness of the max-attainment facet at `d`. -/
theorem encodeMaxAttainAt_sound (val : Valuation S) (hv : val.orderConsistent)
    (js : List (Fin S.nInt)) (mx : Fin S.nInt) (d : Int)
    (hwit : ∃ v ∈ js, val.intValue v = val.intValue mx) :
    (encodeMaxAttainAt js mx d).sat val := by
  have hC := adContrib_eval val hv mx d
  simp only [SignedPBConstr.sat, encodeMaxAttainAt, signedEval_append]
  rw [signedEval_thrGeSum val hv d js]
  by_cases hc : val.intValue mx = d
  · rw [if_pos hc] at hC
    obtain ⟨v₀, hv₀mem, hv₀⟩ := hwit
    have hbound : (js.map (fun v =>
        if val.intValue v ≤ d - 1 then (1 : Int) else 0)).sum
        ≤ (js.length : Int) - 1 := by
      refine sum_ite_pred_le_length_sub_one js _ hv₀mem ?_
      rw [hv₀, hc]
      omega
    linarith
  · rw [if_neg hc] at hC
    have hbound := sum_ite_pred_le_length js (fun v => val.intValue v ≤ d - 1)
    linarith

/-- Soundness of the min-attainment facet at `d`. -/
theorem encodeMinAttainAt_sound (val : Valuation S) (hv : val.orderConsistent)
    (js : List (Fin S.nInt)) (mn : Fin S.nInt) (d : Int)
    (hwit : ∃ v ∈ js, val.intValue v = val.intValue mn) :
    (encodeMinAttainAt js mn d).sat val := by
  have hC := adContrib_eval val hv mn d
  simp only [SignedPBConstr.sat, encodeMinAttainAt, signedEval_append]
  rw [signedEval_thrLeSum val hv d js]
  by_cases hc : val.intValue mn = d
  · rw [if_pos hc] at hC
    obtain ⟨v₀, hv₀mem, hv₀⟩ := hwit
    have hbound : (1 : Int) ≤ (js.map (fun v =>
        if val.intValue v ≤ d then (1 : Int) else 0)).sum := by
      refine one_le_sum_ite_pred js _ hv₀mem ?_
      rw [hv₀, hc]
    linarith
  · rw [if_neg hc] at hC
    have hbound := sum_ite_pred_nonneg js (fun v => val.intValue v ≤ d)
    linarith

/-- `maximum` attainment as a soundness-carrying entry (aux-free): one facet per
    domain value of the target. -/
def encMaxAttain (js : List (Fin S.nInt)) (mx : Fin S.nInt) : EncConstr S where
  constrs := (S.values mx).flatMap
    (fun d => (normalize (encodeMaxAttainAt js mx d)).toList)
  pre := fun a => ∃ v ∈ js, a v = a mx
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hpre _ c hc
    rw [List.mem_flatMap] at hc
    obtain ⟨d, _, hc⟩ := hc
    rw [Option.mem_toList] at hc
    rw [← normalize_sat_iff _ _ hc]
    refine encodeMaxAttainAt_sound (extend a bA auxA)
      (extend_orderConsistent a bA auxA) js mx d ?_
    obtain ⟨v₀, hm, hv₀⟩ := hpre
    refine ⟨v₀, hm, ?_⟩
    rw [extend_intValue a bA auxA hdom v₀, extend_intValue a bA auxA hdom mx]
    exact hv₀

/-- `minimum` attainment as a soundness-carrying entry (aux-free). -/
def encMinAttain (js : List (Fin S.nInt)) (mn : Fin S.nInt) : EncConstr S where
  constrs := (S.values mn).flatMap
    (fun d => (normalize (encodeMinAttainAt js mn d)).toList)
  pre := fun a => ∃ v ∈ js, a v = a mn
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hpre _ c hc
    rw [List.mem_flatMap] at hc
    obtain ⟨d, _, hc⟩ := hc
    rw [Option.mem_toList] at hc
    rw [← normalize_sat_iff _ _ hc]
    refine encodeMinAttainAt_sound (extend a bA auxA)
      (extend_orderConsistent a bA auxA) js mn d ?_
    obtain ⟨v₀, hm, hv₀⟩ := hpre
    refine ⟨v₀, hm, ?_⟩
    rw [extend_intValue a bA auxA hdom v₀, extend_intValue a bA auxA hdom mn]
    exact hv₀

/-- `count` as a soundness-carrying entry (aux-free). -/
def encCount (js : List (Fin S.nInt)) (value : Int) (n : ℕ) : EncConstr S where
  constrs := (normalize (encodeCountGe js value n)).toList
    ++ (normalize (encodeCountLe js value n)).toList
  pre := fun a => ((js.map a).filter (· = value)).length = n
  setsAux := fun _ => []
  sound := by
    intro a bA auxA hdom hpre _ c hc
    have hsum : ((js.map (fun j =>
        if (extend a bA auxA).intValue j = value then (1 : Int) else 0)).sum)
        = (n : Int) := by
      have hmap : js.map (fun j =>
          if (extend a bA auxA).intValue j = value then (1 : Int) else 0)
          = (js.map a).map (fun y => if y = value then (1 : Int) else 0) := by
        rw [List.map_map]
        refine List.map_congr_left (fun j _ => ?_)
        simp only [Function.comp_apply, extend_intValue a bA auxA hdom j]
      rw [hmap, sum_ite_eq_filter_length, hpre]
    have hboth := encodeCount_sound (extend a bA auxA)
      (extend_orderConsistent a bA auxA) js value n hsum
    rw [List.mem_append] at hc
    rcases hc with hc | hc <;> rw [Option.mem_toList] at hc <;>
      rw [← normalize_sat_iff _ _ hc]
    · exact hboth.1
    · exact hboth.2

/-- `encodePattern` extended with a Big-M selector base.  The only constructors that can
    produce an aux-owning entry are the linear / sum / var-target relations with op `.NE`;
    these are routed through `encodeRelAt base`.  Every other constructor delegates to the
    aux-free `encodePattern` (the catch-all arm), so its soundness is reused verbatim. -/
def encodePatternAt (S : CSPSig) (base : ℕ) : IntConstraint S.nInt → List (EncConstr S)
  | .linear vars coeffs op target =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        encodeRelAt S base op (coeffs.zip (toFinList S vars)) target else []
  | .sum vars op target =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        encodeRelAt S base op ((toFinList S vars).map (fun v => ((1 : Int), v))) target else []
  | .sum_rel_var vars op tvar =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ tvar < S.nInt then
        encodeRelAt S base op
          ((toFinList S vars).map (fun v => ((1 : Int), v)) ++ [((-1 : Int), ⟨tvar, h.2⟩)]) 0
      else []
  | .linear_rel_var vars coeffs op tvar =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ tvar < S.nInt then
        encodeRelAt S base op (coeffs.zip (toFinList S vars) ++ [((-1 : Int), ⟨tvar, h.2⟩)]) 0
      else []
  -- Offset all-different (diagonals): one Big-M `≠` per pair of the zipped list.
  | .alldifferentOffset vars offsets =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        encodeOffsetPairs S ((toFinList S vars).zip offsets) base
      else []
  -- `increasing`: the consecutive `≤` chain.
  | .increasing vars =>
      if _ : ∀ v ∈ vars, v < S.nInt then encodeIncreasing S (toFinList S vars) else []
  -- `sliding_sum`: one linear relation per window (`.NE` windows drop via `encodeRel`).
  | .sliding_sum vars w op target =>
      if _ : ∀ v ∈ vars, v < S.nInt then
        (List.range (vars.length - w + 1)).flatMap
          (fun s => encodeRel S op
            ((((toFinList S vars).drop s).take w).map (fun v => ((1 : Int), v))) target)
      else []
  -- `if_then` / `if_then_or`: the indicator implication facets (aux-free, exact).
  | .if_then v value nv nvalue =>
      if h : v < S.nInt ∧ nv < S.nInt then
        [encIfThen ⟨v, h.1⟩ value ⟨nv, h.2⟩ nvalue]
      else []
  | .if_then_or v value nv allowed =>
      if h : v < S.nInt ∧ nv < S.nInt then
        [encIfThenOr ⟨v, h.1⟩ value ⟨nv, h.2⟩ allowed]
      else []
  -- `count`: the indicator-sum equality (aux-free, exact).
  | .count vars value n =>
      if _ : ∀ v ∈ vars, v < S.nInt then [encCount (toFinList S vars) value n] else []
  -- `modulo`: filter the domain — `v ≠ d` for every domain value with the wrong
  -- residue (aux-free, exact).
  | .modulo v n k =>
      if h : v < S.nInt then
        ((S.values ⟨v, h⟩).filter (fun d => decide (¬ d % n = k))).map
          (fun d => encNeConst ⟨v, h⟩ d)
      else []
  -- `element`: index bounds plus one `if_then` implication per array position.
  | .element idx arr res =>
      if h : idx < S.nInt ∧ res < S.nInt then
        encodeRel S .GE [((1 : Int), ⟨idx, h.1⟩)] 1
          ++ encodeRel S .LE [((1 : Int), ⟨idx, h.1⟩)] (arr.length : Int)
          ++ encodeElementCases ⟨idx, h.1⟩ ⟨res, h.2⟩ arr 1
      else []
  -- `abs_diff_rel`: `|v1 − v2| (op) t` — bounds for `≤`/`<`, the gated disjunction
  -- for `≥`/`>`/`=`, two Big-M `≠`s for `≠`; trivial/infeasible `t` handled exactly.
  | .abs_diff_rel v1 v2 .LE t =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        if 0 ≤ t then
          [encLinearLe [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] t,
           encLinearLe [((1 : Int), ⟨v2, h.2⟩), ((-1 : Int), ⟨v1, h.1⟩)] t]
        else [encLinearLe [] (-1)]
      else []
  | .abs_diff_rel v1 v2 .LT t =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        if 0 < t then
          [encLinearLe [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] (t - 1),
           encLinearLe [((1 : Int), ⟨v2, h.2⟩), ((-1 : Int), ⟨v1, h.1⟩)] (t - 1)]
        else [encLinearLe [] (-1)]
      else []
  | .abs_diff_rel v1 v2 .GE t =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        if 0 < t then
          if hb : base < S.nAux then
            [encOrLe [((1 : Int), ⟨v2, h.2⟩), ((-1 : Int), ⟨v1, h.1⟩)] (-t)
              [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] (-t) ⟨base, hb⟩]
          else []
        else []
      else []
  | .abs_diff_rel v1 v2 .GT t =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        if 0 ≤ t then
          if hb : base < S.nAux then
            [encOrLe [((1 : Int), ⟨v2, h.2⟩), ((-1 : Int), ⟨v1, h.1⟩)] (-(t + 1))
              [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] (-(t + 1)) ⟨base, hb⟩]
          else []
        else []
      else []
  | .abs_diff_rel v1 v2 .EQ t =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        if 0 ≤ t then
          if hb : base < S.nAux then
            [encLinearLe [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] t,
             encLinearLe [((1 : Int), ⟨v2, h.2⟩), ((-1 : Int), ⟨v1, h.1⟩)] t,
             encOrLe [((1 : Int), ⟨v2, h.2⟩), ((-1 : Int), ⟨v1, h.1⟩)] (-t)
               [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] (-t) ⟨base, hb⟩]
          else
            [encLinearLe [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] t,
             encLinearLe [((1 : Int), ⟨v2, h.2⟩), ((-1 : Int), ⟨v1, h.1⟩)] t]
        else [encLinearLe [] (-1)]
      else []
  | .abs_diff_rel v1 v2 .NE t =>
      if h : v1 < S.nInt ∧ v2 < S.nInt then
        if 0 ≤ t then
          if hb : base + 1 < S.nAux then
            [encLinearNe [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] t
               ⟨base, by omega⟩,
             encLinearNe [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2⟩)] (-t)
               ⟨base + 1, hb⟩]
          else []
        else []
      else []
  -- `abs_diff_var`: `r = |v1 − v2|` — the two lower bounds plus a gated attainment.
  | .abs_diff_var v1 v2 r =>
      if h : v1 < S.nInt ∧ v2 < S.nInt ∧ r < S.nInt then
        encLinearLe [((1 : Int), ⟨v1, h.1⟩), ((-1 : Int), ⟨v2, h.2.1⟩),
            ((-1 : Int), ⟨r, h.2.2⟩)] 0
          :: encLinearLe [((1 : Int), ⟨v2, h.2.1⟩), ((-1 : Int), ⟨v1, h.1⟩),
              ((-1 : Int), ⟨r, h.2.2⟩)] 0
          :: (if hb : base < S.nAux then
                [encOrLe [((1 : Int), ⟨r, h.2.2⟩), ((-1 : Int), ⟨v1, h.1⟩),
                    ((1 : Int), ⟨v2, h.2.1⟩)] 0
                  [((1 : Int), ⟨r, h.2.2⟩), ((1 : Int), ⟨v1, h.1⟩),
                    ((-1 : Int), ⟨v2, h.2.1⟩)] 0 ⟨base, hb⟩]
              else [])
      else []
  -- `count_var`: gated cardinality per domain value of the count variable.
  | .count_var vars value cvar =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ cvar < S.nInt then
        [encCountVar (toFinList S vars) value ⟨cvar, h.2⟩]
      else []
  -- `maximum`/`minimum`: the per-element bounds (`vᵢ ≤ mx` / `mn ≤ vᵢ`) plus the
  -- attainment facets (`[mx = d] ≤ Σᵥ ⟦v ≥ d⟧` per domain value `d`) — exact.
  | .maximum vars mx =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ mx < S.nInt then
        (toFinList S vars).map
          (fun v => encLinearLe [((1 : Int), v), ((-1 : Int), ⟨mx, h.2⟩)] 0)
        ++ [encMaxAttain (toFinList S vars) ⟨mx, h.2⟩]
      else []
  | .minimum vars mn =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ mn < S.nInt then
        (toFinList S vars).map
          (fun v => encLinearLe [((1 : Int), ⟨mn, h.2⟩), ((-1 : Int), v)] 0)
        ++ [encMinAttain (toFinList S vars) ⟨mn, h.2⟩]
      else []
  -- `not_gate i o`: `o = 1 − i` over `{0,1}` ⟺ `o + i = 1` (aux-free, domain-free).
  | .not_gate i o =>
      if h : i < S.nInt ∧ o < S.nInt then
        encodeRel S .EQ [((1 : Int), ⟨o, h.2⟩), ((1 : Int), ⟨i, h.1⟩)] 1 else []
  -- Boolean gates over `{0,1}` inputs: the exact linear facets.  Each is guarded by a
  -- decidable check that the *input* domains lie in `[0,1]` (the facets are only sound
  -- there); otherwise the gate encodes to `[]` (sound by weakening).
  | .and_gate i1 i2 o =>
      if h : i1 < S.nInt ∧ i2 < S.nInt ∧ o < S.nInt then
        if (∀ x ∈ S.values ⟨i1, h.1⟩, 0 ≤ x ∧ x ≤ 1)
            ∧ (∀ x ∈ S.values ⟨i2, h.2.1⟩, 0 ≤ x ∧ x ≤ 1) then
          [encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩)] 0,
           encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((-1 : Int), ⟨i2, h.2.1⟩)] 0,
           encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((1 : Int), ⟨i2, h.2.1⟩),
             ((-1 : Int), ⟨o, h.2.2⟩)] 1]
        else []
      else []
  | .or_gate i1 i2 o =>
      if h : i1 < S.nInt ∧ i2 < S.nInt ∧ o < S.nInt then
        if (∀ x ∈ S.values ⟨i1, h.1⟩, 0 ≤ x ∧ x ≤ 1)
            ∧ (∀ x ∈ S.values ⟨i2, h.2.1⟩, 0 ≤ x ∧ x ≤ 1) then
          [encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((-1 : Int), ⟨o, h.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨i2, h.2.1⟩), ((-1 : Int), ⟨o, h.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨i2, h.2.1⟩)] 0]
        else []
      else []
  | .xor_gate i1 i2 o =>
      if h : i1 < S.nInt ∧ i2 < S.nInt ∧ o < S.nInt then
        if (∀ x ∈ S.values ⟨i1, h.1⟩, 0 ≤ x ∧ x ≤ 1)
            ∧ (∀ x ∈ S.values ⟨i2, h.2.1⟩, 0 ≤ x ∧ x ≤ 1) then
          [encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨i2, h.2.1⟩)] 0,
           encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((-1 : Int), ⟨i2, h.2.1⟩),
             ((-1 : Int), ⟨o, h.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨i2, h.2.1⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨o, h.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((1 : Int), ⟨i1, h.1⟩),
             ((1 : Int), ⟨i2, h.2.1⟩)] 2]
        else []
      else []
  -- `nand`/`nor`: their `patternHolds` is *already* a conjunction of linear bounds.
  | .nand_gate i1 i2 o =>
      if h : i1 < S.nInt ∧ i2 < S.nInt ∧ o < S.nInt then
        [encLinearLe [((-1 : Int), ⟨o, h.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩)] (-1),
         encLinearLe [((-1 : Int), ⟨o, h.2.2⟩), ((-1 : Int), ⟨i2, h.2.1⟩)] (-1),
         encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((1 : Int), ⟨i1, h.1⟩),
           ((1 : Int), ⟨i2, h.2.1⟩)] 2]
      else []
  | .nor_gate i1 i2 o =>
      if h : i1 < S.nInt ∧ i2 < S.nInt ∧ o < S.nInt then
        [encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((1 : Int), ⟨i1, h.1⟩)] 1,
         encLinearLe [((1 : Int), ⟨o, h.2.2⟩), ((1 : Int), ⟨i2, h.2.1⟩)] 1,
         encLinearLe [((-1 : Int), ⟨o, h.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩),
           ((-1 : Int), ⟨i2, h.2.1⟩)] (-1)]
      else []
  -- Binary parity: the 4 XOR facets (same as `xor_gate`).
  | .xor_all [i1, i2] r =>
      if h : i1 < S.nInt ∧ i2 < S.nInt ∧ r < S.nInt then
        if (∀ x ∈ S.values ⟨i1, h.1⟩, 0 ≤ x ∧ x ≤ 1)
            ∧ (∀ x ∈ S.values ⟨i2, h.2.1⟩, 0 ≤ x ∧ x ≤ 1) then
          [encLinearLe [((1 : Int), ⟨r, h.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨i2, h.2.1⟩)] 0,
           encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((-1 : Int), ⟨i2, h.2.1⟩),
             ((-1 : Int), ⟨r, h.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨i2, h.2.1⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨r, h.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨r, h.2.2⟩), ((1 : Int), ⟨i1, h.1⟩),
             ((1 : Int), ⟨i2, h.2.1⟩)] 2]
        else []
      else []
  -- Ternary parity: the 8 facets of the XOR polytope (full-adder sum).
  | .xor_all [i1, i2, i3] r =>
      if h : i1 < S.nInt ∧ i2 < S.nInt ∧ i3 < S.nInt ∧ r < S.nInt then
        if (∀ x ∈ S.values ⟨i1, h.1⟩, 0 ≤ x ∧ x ≤ 1)
            ∧ (∀ x ∈ S.values ⟨i2, h.2.1⟩, 0 ≤ x ∧ x ≤ 1)
            ∧ (∀ x ∈ S.values ⟨i3, h.2.2.1⟩, 0 ≤ x ∧ x ≤ 1) then
          [encLinearLe [((1 : Int), ⟨r, h.2.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨i2, h.2.1⟩), ((-1 : Int), ⟨i3, h.2.2.1⟩)] 0,
           encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((-1 : Int), ⟨i2, h.2.1⟩),
             ((-1 : Int), ⟨i3, h.2.2.1⟩), ((-1 : Int), ⟨r, h.2.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨i2, h.2.1⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨i3, h.2.2.1⟩), ((-1 : Int), ⟨r, h.2.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨i3, h.2.2.1⟩), ((-1 : Int), ⟨i1, h.1⟩),
             ((-1 : Int), ⟨i2, h.2.1⟩), ((-1 : Int), ⟨r, h.2.2.2⟩)] 0,
           encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((1 : Int), ⟨i2, h.2.1⟩),
             ((1 : Int), ⟨i3, h.2.2.1⟩), ((-1 : Int), ⟨r, h.2.2.2⟩)] 2,
           encLinearLe [((1 : Int), ⟨i2, h.2.1⟩), ((1 : Int), ⟨i3, h.2.2.1⟩),
             ((1 : Int), ⟨r, h.2.2.2⟩), ((-1 : Int), ⟨i1, h.1⟩)] 2,
           encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((1 : Int), ⟨i3, h.2.2.1⟩),
             ((1 : Int), ⟨r, h.2.2.2⟩), ((-1 : Int), ⟨i2, h.2.1⟩)] 2,
           encLinearLe [((1 : Int), ⟨i1, h.1⟩), ((1 : Int), ⟨i2, h.2.1⟩),
             ((1 : Int), ⟨r, h.2.2.2⟩), ((-1 : Int), ⟨i3, h.2.2.1⟩)] 2]
        else []
      else []
  -- Multi-input AND/OR: per-input bound plus the sum bound (min/max facets).
  | .and_all vars r =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ r < S.nInt then
        if ∀ j ∈ toFinList S vars, ∀ x ∈ S.values j, 0 ≤ x ∧ x ≤ 1 then
          (toFinList S vars).map
              (fun v => encLinearLe [((1 : Int), ⟨r, h.2⟩), ((-1 : Int), v)] 0)
            ++ [encLinearLe ((toFinList S vars).map (fun v => ((1 : Int), v))
                  ++ [((-1 : Int), ⟨r, h.2⟩)]) ((vars.length : Int) - 1)]
        else []
      else []
  | .or_all vars r =>
      if h : (∀ v ∈ vars, v < S.nInt) ∧ r < S.nInt then
        if ∀ j ∈ toFinList S vars, ∀ x ∈ S.values j, 0 ≤ x ∧ x ≤ 1 then
          (toFinList S vars).map
              (fun v => encLinearLe [((1 : Int), v), ((-1 : Int), ⟨r, h.2⟩)] 0)
            ++ [encLinearLe (((1 : Int), (⟨r, h.2⟩ : Fin S.nInt))
                  :: (toFinList S vars).map (fun v => ((-1 : Int), v))) 0]
        else []
      else []
  -- `strictLexRevLeader`: the base-3 mirror `≠` (one Big-M selector), only over `{0,1,2}`
  -- domains (where the encoding is a sound relaxation of `x <_lex rev x`); dropped otherwise.
  | .strictLexRevLeader =>
      if hg : ∀ i : Fin S.nInt, S.values i = [0, 1, 2] then
        if hb : base < S.nAux then [encStrictLexRev S base hb hg] else []
      else []
  | c => encodePattern S c

/-- Soundness of `encodePatternAt`: each emitted entry's precondition follows from
    `patternHolds c a`.  The four NE-capable cases use `encodeRelAt_sound`; the rest
    delegate to `encodePattern_sound` (their `encodePatternAt` is *definitionally* the
    `encodePattern` value via the catch-all arm). -/
theorem encodePatternAt_sound (base : ℕ) (c : IntConstraint S.nInt) (a : Fin S.nInt → Int)
    (hdom : ∀ i, a i ∈ S.values i) (hpat : patternHolds c a)
    (e : EncConstr S) (he : e ∈ encodePatternAt S base c) :
    e.pre a := by
  cases c
  case linear vars coeffs op target =>
      simp only [encodePatternAt] at he; split at he
      · rename_i hwf
        refine encodeRelAt_sound base op (coeffs.zip (toFinList S vars)) target a ?_ e he
        rw [linTerms_sum a coeffs vars hwf]; exact hpat
      · exact absurd he (by simp)
  case sum vars op target =>
      simp only [encodePatternAt] at he; split at he
      · rename_i hwf
        refine encodeRelAt_sound base op ((toFinList S vars).map (fun v => ((1 : Int), v)))
          target a ?_ e he
        rw [unitTerms_sum a vars hwf]; exact hpat
      · exact absurd he (by simp)
  case sum_rel_var vars op tvar =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        refine encodeRelAt_var_sound base op ((toFinList S vars).map (fun v => ((1 : Int), v)))
          ⟨tvar, h.2⟩ a ((vars.map (valAt a)).sum) (unitTerms_sum a vars h.1) ?_ e he
        have hh : relHolds op ((vars.map (valAt a)).sum) (valAt a tvar) := hpat
        simpa only [valAt, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case linear_rel_var vars coeffs op tvar =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        refine encodeRelAt_var_sound base op (coeffs.zip (toFinList S vars)) ⟨tvar, h.2⟩ a
          (List.zipWith (· * ·) coeffs (vars.map (valAt a))).sum
          (linTerms_sum a coeffs vars h.1) ?_ e he
        have hh : relHolds op
          (List.zipWith (· * ·) coeffs (vars.map (valAt a))).sum (valAt a tvar) := hpat
        simpa only [valAt, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case alldifferentOffset vars offsets =>
      simp only [encodePatternAt] at he; split at he
      · rename_i hwf
        refine encodeOffsetPairs_sound ((toFinList S vars).zip offsets) base a ?_ e he
        have hnd : ((vars.zip offsets).map (fun p => valAt a p.1 + p.2)).Nodup := hpat
        have hpw0 : List.Pairwise
            (fun p q => valAt a p.1 + p.2 ≠ valAt a q.1 + q.2) (vars.zip offsets) :=
          List.pairwise_map.mp hnd
        have hzip : ((toFinList S vars).zip offsets).map (Prod.map Fin.val id)
            = vars.zip offsets := by
          rw [← List.zip_map_left, toFinList_val vars hwf]
        rw [← hzip] at hpw0
        have hpw1 := List.pairwise_map.mp hpw0
        refine hpw1.imp ?_
        intro p q hne
        obtain ⟨pf, po⟩ := p
        obtain ⟨qf, qo⟩ := q
        simpa only [Prod.map, id, valAt, pf.isLt, qf.isLt, dite_true, Fin.eta] using hne
      · exact absurd he (by simp)
  case increasing vars =>
      simp only [encodePatternAt] at he; split at he
      · rename_i hwf
        refine encodeIncreasing_sound (toFinList S vars) a ?_ e he
        rw [toFinList_map a vars hwf]
        exact hpat
      · exact absurd he (by simp)
  case sliding_sum vars w op target =>
      simp only [encodePatternAt] at he; split at he
      · rename_i hwf
        rw [List.mem_flatMap] at he
        obtain ⟨s, hs, he⟩ := he
        refine encodeRel_sound op _ target a ?_ e he
        have hp : relHolds op ((((vars.map (valAt a)).drop s).take w)).sum target :=
          hpat s hs
        have hsum : ((((((toFinList S vars).drop s).take w)).map
            (fun v => ((1 : Int), v))).map (fun p => p.1 * a p.2)).sum
            = (((vars.map (valAt a)).drop s).take w).sum := by
          rw [List.map_map]
          have h1 : ((((toFinList S vars).drop s).take w)).map
              ((fun p => p.1 * a p.2) ∘ (fun v => ((1 : Int), v)))
              = (((toFinList S vars).drop s).take w).map a :=
            List.map_congr_left (fun v _ => by simp)
          rw [h1, List.map_take, List.map_drop, toFinList_map a vars hwf]
        rw [hsum]
        exact hp
      · exact absurd he (by simp)
  case if_then v value nv nvalue =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        rw [List.mem_singleton] at he; subst he
        show a ⟨v, h.1⟩ ≠ value ∨ a ⟨nv, h.2⟩ = nvalue
        have hh : valAt a v ≠ value ∨ valAt a nv = nvalue := hpat
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case if_then_or v value nv allowed =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        rw [List.mem_singleton] at he; subst he
        show a ⟨v, h.1⟩ ≠ value ∨ a ⟨nv, h.2⟩ ∈ allowed
        have hh : valAt a v ≠ value ∨ valAt a nv ∈ allowed := hpat
        simpa only [valAt, h.1, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case count vars value n =>
      simp only [encodePatternAt] at he; split at he
      · rename_i hwf
        rw [List.mem_singleton] at he; subst he
        show (((toFinList S vars).map a).filter (· = value)).length = n
        rw [toFinList_map a vars hwf]
        exact hpat
      · exact absurd he (by simp)
  case count_var vars value cvar =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        rw [List.mem_singleton] at he; subst he
        show ((((toFinList S vars).map a).filter (· = value)).length : Int)
          = a ⟨cvar, h.2⟩
        rw [toFinList_map a vars h.1]
        have hh : ((((vars.map (valAt a))).filter (· = value)).length : Int)
            = valAt a cvar := hpat
        simpa only [valAt, h.2, dite_true] using hh
      · exact absurd he (by simp)
  case modulo v n k =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp he
        rw [List.mem_filter] at hdmem
        have hdneq : ¬ d % n = k := by
          have := hdmem.2
          simpa using this
        show a ⟨v, h⟩ ≠ d
        intro hcontra
        have hh : valAt a v % n = k := hpat
        rw [show valAt a v = a ⟨v, h⟩ from by simp [valAt, h], hcontra] at hh
        exact hdneq hh
      · exact absurd he (by simp)
  case element idx arr res =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        obtain ⟨hge1, hany⟩ := (hpat : valAt a idx ≥ 1 ∧
          (arr[(valAt a idx).natAbs - 1]?).any (· = valAt a res) = true)
        have hidxa : valAt a idx = a ⟨idx, h.1⟩ := by simp [valAt, h.1]
        have hresa : valAt a res = a ⟨res, h.2⟩ := by simp [valAt, h.2]
        -- the looked-up entry exists and equals `res`
        rcases harr : arr[(valAt a idx).natAbs - 1]? with _ | y
        · rw [harr] at hany
          simp at hany
        have hyres : y = valAt a res := by
          rw [harr] at hany
          simpa using hany
        have hlt : (valAt a idx).natAbs - 1 < arr.length :=
          (List.getElem?_eq_some_iff.mp harr).1
        rw [List.mem_append, List.mem_append] at he
        rcases he with (he | he) | he
        · refine encodeRel_unary_sound .GE ⟨idx, h.1⟩ 1 a ?_ e he
          show a ⟨idx, h.1⟩ ≥ 1
          omega
        · refine encodeRel_unary_sound .LE ⟨idx, h.1⟩ (arr.length : Int) a ?_ e he
          show a ⟨idx, h.1⟩ ≤ (arr.length : Int)
          omega
        · refine encodeElementCases_sound ⟨idx, h.1⟩ ⟨res, h.2⟩ arr 1 a ?_ e he
          intro q y' hq hidxq
          have hnat : (valAt a idx).natAbs - 1 = q := by
            rw [hidxa, hidxq]
            omega
          rw [hnat, hq] at harr
          rw [← hresa, ← hyres]
          injection harr with hyy
          rw [hyy]
      · exact absurd he (by simp)
  case abs_diff_rel v1 v2 op t =>
      have hD : relHolds op (((valAt a v1 - valAt a v2).natAbs : Int)) t := hpat
      cases op
      case LE =>
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          simp only [relHolds, valAt, h.1, h.2, dite_true] at hD
          split at he <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          · rcases he with rfl | rfl <;>
              simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil] <;> omega
          · subst he
            show (([] : List (Int × Fin S.nInt)).map (fun p => p.1 * a p.2)).sum ≤ -1
            rename_i ht
            simp only [List.map_nil, List.sum_nil]
            omega
        · exact absurd he (by simp)
      case LT =>
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          simp only [relHolds, valAt, h.1, h.2, dite_true] at hD
          split at he <;>
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          · rcases he with rfl | rfl <;>
              simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil] <;> omega
          · subst he
            show (([] : List (Int × Fin S.nInt)).map (fun p => p.1 * a p.2)).sum ≤ -1
            rename_i ht
            simp only [List.map_nil, List.sum_nil]
            omega
        · exact absurd he (by simp)
      case GE =>
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          simp only [relHolds, valAt, h.1, h.2, dite_true] at hD
          split at he
          · split at he
            · simp only [List.mem_singleton] at he
              subst he
              show _ ∨ _
              simp only [List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil]
              omega
            · exact absurd he (by simp)
          · exact absurd he (by simp)
        · exact absurd he (by simp)
      case GT =>
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          simp only [relHolds, valAt, h.1, h.2, dite_true] at hD
          split at he
          · split at he
            · simp only [List.mem_singleton] at he
              subst he
              show _ ∨ _
              simp only [List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil]
              omega
            · exact absurd he (by simp)
          · exact absurd he (by simp)
        · exact absurd he (by simp)
      case EQ =>
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          simp only [relHolds, valAt, h.1, h.2, dite_true] at hD
          split at he
          · split at he <;>
              simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            · rcases he with rfl | rfl | rfl
              · show (([((1 : Int), (⟨v1, h.1⟩ : Fin S.nInt)),
                  ((-1 : Int), ⟨v2, h.2⟩)]).map (fun p => p.1 * a p.2)).sum ≤ t
                simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
                omega
              · show (([((1 : Int), (⟨v2, h.2⟩ : Fin S.nInt)),
                  ((-1 : Int), ⟨v1, h.1⟩)]).map (fun p => p.1 * a p.2)).sum ≤ t
                simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
                omega
              · show _ ∨ _
                simp only [List.map_cons, List.map_nil, List.sum_cons,
                  List.sum_nil]
                omega
            · rcases he with rfl | rfl <;>
                simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
                  List.sum_nil] <;> omega
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            subst he
            show (([] : List (Int × Fin S.nInt)).map (fun p => p.1 * a p.2)).sum ≤ -1
            rename_i ht
            simp only [List.map_nil, List.sum_nil]
            omega
        · exact absurd he (by simp)
      case NE =>
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          simp only [relHolds, valAt, h.1, h.2, dite_true] at hD
          split at he
          · split at he
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              rcases he with rfl | rfl <;>
                (show ¬ _ = _
                 simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
                 omega)
            · exact absurd he (by simp)
          · exact absurd he (by simp)
        · exact absurd he (by simp)
  case abs_diff_var v1 v2 r =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        have hR : valAt a r = ((valAt a v1 - valAt a v2).natAbs : Int) := hpat
        simp only [valAt, h.1, h.2.1, h.2.2, dite_true] at hR
        simp only [List.mem_cons] at he
        rcases he with rfl | rfl | he
        · show (([((1 : Int), (⟨v1, h.1⟩ : Fin S.nInt)), ((-1 : Int), ⟨v2, h.2.1⟩),
            ((-1 : Int), ⟨r, h.2.2⟩)]).map (fun p => p.1 * a p.2)).sum ≤ 0
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          omega
        · show (([((1 : Int), (⟨v2, h.2.1⟩ : Fin S.nInt)), ((-1 : Int), ⟨v1, h.1⟩),
            ((-1 : Int), ⟨r, h.2.2⟩)]).map (fun p => p.1 * a p.2)).sum ≤ 0
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
          omega
        · split at he
          · simp only [List.mem_singleton] at he
            subst he
            show _ ∨ _
            simp only [List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil]
            omega
          · exact absurd he (by simp)
      · exact absurd he (by simp)
  case maximum vars mx =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        rw [List.mem_append] at he
        rcases he with he | he
        · obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp he
          show ([((1 : Int), v), ((-1 : Int), (⟨mx, h.2⟩ : Fin S.nInt))].map
            (fun p => p.1 * a p.2)).sum ≤ 0
          have hall : ∀ y ∈ vars.map (valAt a), y ≤ valAt a mx := by
            have h1 := (hpat : _ ∧ _).1
            rw [List.all_eq_true] at h1
            intro y hy
            exact decide_eq_true_eq.mp (h1 y hy)
          have hav : a v ∈ vars.map (valAt a) := by
            rw [← toFinList_map a vars h.1]
            exact List.mem_map.mpr ⟨v, hvmem, rfl⟩
          have hb := hall _ hav
          have hmx : valAt a mx = a ⟨mx, h.2⟩ := by simp [valAt, h.2]
          rw [binTerms_sum]
          omega
        · rw [List.mem_singleton] at he; subst he
          show ∃ v ∈ toFinList S vars, a v = a ⟨mx, h.2⟩
          have h2 := (hpat : _ ∧ _).2
          rw [List.any_eq_true] at h2
          obtain ⟨y, hy, hdec⟩ := h2
          obtain ⟨w, hwmem, rfl⟩ := List.mem_map.mp hy
          have hw : w < S.nInt := h.1 w hwmem
          refine ⟨⟨w, hw⟩, mem_toFinList hw hwmem, ?_⟩
          have heq : valAt a w = valAt a mx := decide_eq_true_eq.mp hdec
          simpa only [valAt, hw, h.2, dite_true] using heq
      · exact absurd he (by simp)
  case minimum vars mn =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        rw [List.mem_append] at he
        rcases he with he | he
        · obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp he
          show ([((1 : Int), (⟨mn, h.2⟩ : Fin S.nInt)), ((-1 : Int), v)].map
            (fun p => p.1 * a p.2)).sum ≤ 0
          have hall : ∀ y ∈ vars.map (valAt a), valAt a mn ≤ y := by
            have h1 := (hpat : _ ∧ _).1
            rw [List.all_eq_true] at h1
            intro y hy
            exact decide_eq_true_eq.mp (h1 y hy)
          have hav : a v ∈ vars.map (valAt a) := by
            rw [← toFinList_map a vars h.1]
            exact List.mem_map.mpr ⟨v, hvmem, rfl⟩
          have hb := hall _ hav
          have hmn : valAt a mn = a ⟨mn, h.2⟩ := by simp [valAt, h.2]
          rw [binTerms_sum]
          omega
        · rw [List.mem_singleton] at he; subst he
          show ∃ v ∈ toFinList S vars, a v = a ⟨mn, h.2⟩
          have h2 := (hpat : _ ∧ _).2
          rw [List.any_eq_true] at h2
          obtain ⟨y, hy, hdec⟩ := h2
          obtain ⟨w, hwmem, rfl⟩ := List.mem_map.mp hy
          have hw : w < S.nInt := h.1 w hwmem
          refine ⟨⟨w, hw⟩, mem_toFinList hw hwmem, ?_⟩
          have heq : valAt a w = valAt a mn := decide_eq_true_eq.mp hdec
          simpa only [valAt, hw, h.2, dite_true] using heq
      · exact absurd he (by simp)
  case not_gate i o =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        refine encodeRel_sound .EQ [((1 : Int), ⟨o, h.2⟩), ((1 : Int), ⟨i, h.1⟩)] 1 a ?_ e he
        have hh : valAt a o = 1 - valAt a i := hpat
        simp only [valAt, h.1, h.2, dite_true] at hh
        show ([((1 : Int), (⟨o, h.2⟩ : Fin S.nInt)), ((1 : Int), ⟨i, h.1⟩)].map
          (fun p => p.1 * a p.2)).sum = 1
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega
      · exact absurd he (by simp)
  case and_gate i1 i2 o =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        split at he
        · rename_i hd
          have hp : a ⟨o, h.2.2⟩ = min (a ⟨i1, h.1⟩) (a ⟨i2, h.2.1⟩) := by
            have hh : valAt a o = min (valAt a i1) (valAt a i2) := hpat
            simpa only [valAt, h.1, h.2.1, h.2.2, dite_true] using hh
          have hfacts := and2_bounds _ _ _ (hd.1 _ (hdom ⟨i1, h.1⟩))
            (hd.2 _ (hdom ⟨i2, h.2.1⟩)) hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl <;>
            simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] <;> omega
        · exact absurd he (by simp)
      · exact absurd he (by simp)
  case or_gate i1 i2 o =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        split at he
        · rename_i hd
          have hp : a ⟨o, h.2.2⟩ = max (a ⟨i1, h.1⟩) (a ⟨i2, h.2.1⟩) := by
            have hh : valAt a o = max (valAt a i1) (valAt a i2) := hpat
            simpa only [valAt, h.1, h.2.1, h.2.2, dite_true] using hh
          have hfacts := or2_bounds _ _ _ (hd.1 _ (hdom ⟨i1, h.1⟩))
            (hd.2 _ (hdom ⟨i2, h.2.1⟩)) hp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl <;>
            simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] <;> omega
        · exact absurd he (by simp)
      · exact absurd he (by simp)
  case xor_gate i1 i2 o =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        split at he
        · rename_i hd
          have hp : (a ⟨i1, h.1⟩ + a ⟨i2, h.2.1⟩) % 2 = a ⟨o, h.2.2⟩ := by
            have hh : (valAt a i1 + valAt a i2) % 2 = valAt a o := hpat
            simpa only [valAt, h.1, h.2.1, h.2.2, dite_true] using hh
          have hb1 := hd.1 _ (hdom ⟨i1, h.1⟩)
          have hb2 := hd.2 _ (hdom ⟨i2, h.2.1⟩)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl <;>
            simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil] <;> omega
        · exact absurd he (by simp)
      · exact absurd he (by simp)
  case nand_gate i1 i2 o =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        have hp : a ⟨o, h.2.2⟩ ≥ 1 - a ⟨i1, h.1⟩ ∧ a ⟨o, h.2.2⟩ ≥ 1 - a ⟨i2, h.2.1⟩ ∧
            a ⟨o, h.2.2⟩ ≤ 2 - a ⟨i1, h.1⟩ - a ⟨i2, h.2.1⟩ := by
          have hh : valAt a o ≥ 1 - valAt a i1 ∧ valAt a o ≥ 1 - valAt a i2 ∧
              valAt a o ≤ 2 - valAt a i1 - valAt a i2 := hpat
          simpa only [valAt, h.1, h.2.1, h.2.2, dite_true] using hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;>
          simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil] <;> omega
      · exact absurd he (by simp)
  case nor_gate i1 i2 o =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        have hp : a ⟨o, h.2.2⟩ ≤ 1 - a ⟨i1, h.1⟩ ∧ a ⟨o, h.2.2⟩ ≤ 1 - a ⟨i2, h.2.1⟩ ∧
            a ⟨o, h.2.2⟩ ≥ 1 - a ⟨i1, h.1⟩ - a ⟨i2, h.2.1⟩ := by
          have hh : valAt a o ≤ 1 - valAt a i1 ∧ valAt a o ≤ 1 - valAt a i2 ∧
              valAt a o ≥ 1 - valAt a i1 - valAt a i2 := hpat
          simpa only [valAt, h.1, h.2.1, h.2.2, dite_true] using hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;>
          simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil] <;> omega
      · exact absurd he (by simp)
  case xor_all vars r =>
      rcases vars with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, _ | ⟨i4, rest⟩⟩⟩⟩
      · exact encodePattern_sound _ a hpat e he
      · exact encodePattern_sound _ a hpat e he
      · -- binary parity: the 4 XOR facets
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          split at he
          · rename_i hd
            have hp : (a ⟨i1, h.1⟩ + a ⟨i2, h.2.1⟩) % 2 = a ⟨r, h.2.2⟩ := by
              have hh : ([i1, i2].map (valAt a)).sum % 2 = valAt a r := hpat
              simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                add_zero, valAt, h.1, h.2.1, h.2.2, dite_true] using hh
            have hb1 := hd.1 _ (hdom ⟨i1, h.1⟩)
            have hb2 := hd.2 _ (hdom ⟨i2, h.2.1⟩)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl | rfl | rfl <;>
              simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil] <;> omega
          · exact absurd he (by simp)
        · exact absurd he (by simp)
      · -- ternary parity: the 8 facets of the XOR polytope (full-adder sum)
        simp only [encodePatternAt] at he; split at he
        · rename_i h
          split at he
          · rename_i hd
            have hp : (a ⟨i1, h.1⟩ + a ⟨i2, h.2.1⟩ + a ⟨i3, h.2.2.1⟩) % 2
                = a ⟨r, h.2.2.2⟩ := by
              have hh : ([i1, i2, i3].map (valAt a)).sum % 2 = valAt a r := hpat
              have hh' : (valAt a i1 + (valAt a i2 + valAt a i3)) % 2 = valAt a r := by
                simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
                  add_zero] using hh
              simp only [valAt, h.1, h.2.1, h.2.2.1, h.2.2.2, dite_true] at hh'
              omega
            have hb1 := hd.1 _ (hdom ⟨i1, h.1⟩)
            have hb2 := hd.2.1 _ (hdom ⟨i2, h.2.1⟩)
            have hb3 := hd.2.2 _ (hdom ⟨i3, h.2.2.1⟩)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at he
            rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              simp only [encLinearLe, List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil] <;> omega
          · exact absurd he (by simp)
        · exact absurd he (by simp)
      · exact encodePattern_sound _ a hpat e he
  case and_all vars r =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        split at he
        · rename_i hd
          obtain ⟨hne, hfold⟩ := (hpat : (vars.map (valAt a)) ≠ [] ∧
            valAt a r = (vars.map (valAt a)).foldl
              (fun acc x => if x < acc then x else acc) (vars.map (valAt a)).headI)
          rcases hL : vars.map (valAt a) with _ | ⟨m, ms⟩
          · exact absurd hL hne
          rw [hL] at hfold
          have h01 : ∀ y ∈ m :: ms, 0 ≤ y ∧ y ≤ 1 := by
            intro y hy
            rw [← hL] at hy
            obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp hy
            have hv : v < S.nInt := h.1 v hvmem
            have hva : valAt a v = a ⟨v, hv⟩ := by simp [valAt, hv]
            rw [hva]
            exact hd _ (mem_toFinList hv hvmem) _ (hdom ⟨v, hv⟩)
          obtain ⟨hub, hlb⟩ := andAll_bounds m ms (valAt a r) h01 hfold
          have hvr : valAt a r = a ⟨r, h.2⟩ := by simp [valAt, h.2]
          rw [List.mem_append] at he
          rcases he with he | he
          · obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp he
            show ([((1 : Int), (⟨r, h.2⟩ : Fin S.nInt)), ((-1 : Int), v)].map
              (fun p => p.1 * a p.2)).sum ≤ 0
            have hav : a v ∈ m :: ms := by
              rw [← hL, ← toFinList_map a vars h.1]
              exact List.mem_map.mpr ⟨v, hvmem, rfl⟩
            have hr := hub _ hav
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
            omega
          · rw [List.mem_singleton] at he; subst he
            show (((toFinList S vars).map (fun v => ((1 : Int), v))
              ++ [((-1 : Int), (⟨r, h.2⟩ : Fin S.nInt))]).map (fun p => p.1 * a p.2)).sum
              ≤ (vars.length : Int) - 1
            rw [appendNeg_sum, unitTerms_sum a vars h.1, hL]
            have hlen : vars.length = ms.length + 1 := by
              have := congrArg List.length hL
              simpa using this
            simp only [List.sum_cons] at hlb ⊢
            omega
        · exact absurd he (by simp)
      · exact absurd he (by simp)
  case or_all vars r =>
      simp only [encodePatternAt] at he; split at he
      · rename_i h
        split at he
        · rename_i hd
          obtain ⟨hne, hfold⟩ := (hpat : (vars.map (valAt a)) ≠ [] ∧
            valAt a r = (vars.map (valAt a)).foldl
              (fun acc x => if x > acc then x else acc) (vars.map (valAt a)).headI)
          rcases hL : vars.map (valAt a) with _ | ⟨m, ms⟩
          · exact absurd hL hne
          rw [hL] at hfold
          have h0 : ∀ y ∈ m :: ms, 0 ≤ y := by
            intro y hy
            rw [← hL] at hy
            obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp hy
            have hv : v < S.nInt := h.1 v hvmem
            have hva : valAt a v = a ⟨v, hv⟩ := by simp [valAt, hv]
            rw [hva]
            exact (hd _ (mem_toFinList hv hvmem) _ (hdom ⟨v, hv⟩)).1
          obtain ⟨hub, hlb⟩ := orAll_bounds m ms (valAt a r) h0 hfold
          have hvr : valAt a r = a ⟨r, h.2⟩ := by simp [valAt, h.2]
          rw [List.mem_append] at he
          rcases he with he | he
          · obtain ⟨v, hvmem, rfl⟩ := List.mem_map.mp he
            show ([((1 : Int), v), ((-1 : Int), (⟨r, h.2⟩ : Fin S.nInt))].map
              (fun p => p.1 * a p.2)).sum ≤ 0
            have hav : a v ∈ m :: ms := by
              rw [← hL, ← toFinList_map a vars h.1]
              exact List.mem_map.mpr ⟨v, hvmem, rfl⟩
            have hr := hub _ hav
            simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
            omega
          · rw [List.mem_singleton] at he; subst he
            show (((((1 : Int), (⟨r, h.2⟩ : Fin S.nInt)))
              :: (toFinList S vars).map (fun v => ((-1 : Int), v))).map
                (fun p => p.1 * a p.2)).sum ≤ 0
            rw [List.map_cons, List.sum_cons, negUnitTerms_sum a vars h.1, hL]
            simp only [List.sum_cons] at hlb ⊢
            omega
        · exact absurd he (by simp)
      · exact absurd he (by simp)
  case strictLexRevLeader =>
      simp only [encodePatternAt] at he
      by_cases hg : ∀ i : Fin S.nInt, S.values i = [0, 1, 2]
      · rw [dif_pos hg] at he
        by_cases hb : base < S.nAux
        · rw [dif_pos hb, List.mem_singleton] at he
          subst he
          simp only [patternHolds] at hpat
          obtain ⟨p, _, hp⟩ := hpat
          exact ⟨p, ne_of_lt hp⟩
        · rw [dif_neg hb] at he; exact absurd he (by simp)
      · rw [dif_neg hg] at he; exact absurd he (by simp)
  all_goals exact encodePattern_sound _ a hpat e he

/-! ### The combined encoding and the generic theorem -/

/-- Encode a constraint list, threading the Big-M selector base: each constraint is
    encoded at the running sum of the preceding constraints' `auxCount`, so the selector
    blocks owned across the whole list are pairwise disjoint *by construction*. -/
def encodeConstraints (S : CSPSig) : List (IntConstraint S.nInt) → ℕ → List (EncConstr S)
  | [], _ => []
  | c :: cs, base => encodePatternAt S base c ++ encodeConstraints S cs (base + auxCount c)

/-- The full PB constraint set of `csp` (combined with the order-encoding staircase in the
    final formula): every constraint's encoding, selector bases threaded from `0`. -/
def encodeCSP (csp : IntCSP) : List (EncConstr (cspSig csp)) :=
  encodeConstraints (cspSig csp) csp.constraints 0

/-! ### Generic selector distinctness (no per-instance obligation)

The owned selector keys of `encodeCSP` are pairwise distinct *generically*: each
constraint owns at most the single key at its own base (`encodePatternAt_keys_eq`), and
the threaded fold places later constraints at strictly larger bases.  This discharges the
allocator spine's `Nodup` obligation once and for all — no `decide`, no `native_decide`,
no per-problem hypothesis. -/

/-- The owned selector keys of `encodeRelAt` (assignment-free): the `≠` selector, or none. -/
theorem encodeRelAt_keys (base : ℕ) (op : RelOp) (terms : List (Int × Fin S.nInt))
    (target : Int) (a : Fin S.nInt → Int) :
    ((encodeRelAt S base op terms target).flatMap (·.setsAux a)).map Prod.fst
      = (match op with
         | .NE => if h : base < S.nAux then [(⟨base, h⟩ : Fin S.nAux)] else []
         | _ => []) := by
  cases op <;> simp only [encodeRelAt]
  case NE => split <;> simp [encLinearNe]
  all_goals simp [encLinearLe, encLinearGe, encLinearLt, encLinearGt, encLinearEq]

/-- Keys block of the head pairing: `Nodup`, within `[base, base + l.length)`. -/
theorem encodeOffsetHead_keys (v : Fin S.nInt) (o : ℤ) (l : List (Fin S.nInt × ℤ))
    (base : ℕ) (a : Fin S.nInt → Int) :
    (((encodeOffsetHead S v o l base).flatMap (·.setsAux a)).map Prod.fst).Nodup ∧
      ∀ k : Fin S.nAux,
        k ∈ ((encodeOffsetHead S v o l base).flatMap (·.setsAux a)).map Prod.fst →
          base ≤ k.val ∧ k.val < base + l.length := by
  induction l generalizing base with
  | nil => constructor <;> simp [encodeOffsetHead]
  | cons hd rest ih =>
    obtain ⟨w, p⟩ := hd
    obtain ⟨ihnd, ihrange⟩ := ih (base + 1)
    simp only [encodeOffsetHead, List.flatMap_append, List.map_append, List.length_cons]
    rw [encodeRelAt_keys]
    by_cases hb : base < S.nAux
    · rw [dif_pos hb]
      refine ⟨?_, ?_⟩
      · rw [List.singleton_append]
        refine List.nodup_cons.mpr ⟨fun hmem => ?_, ihnd⟩
        have := (ihrange _ hmem).1
        have hv : ((⟨base, hb⟩ : Fin S.nAux) : ℕ) = base := rfl
        omega
      · intro k hk
        rw [List.singleton_append, List.mem_cons] at hk
        rcases hk with rfl | hk
        · have hv : ((⟨base, hb⟩ : Fin S.nAux) : ℕ) = base := rfl
          omega
        · have := ihrange k hk
          omega
    · rw [dif_neg hb, List.nil_append]
      refine ⟨ihnd, fun k hk => ?_⟩
      have := ihrange k hk
      omega

/-- Keys block of the pairwise expansion: `Nodup`, within `[base, base + pairAux |l|)`. -/
theorem encodeOffsetPairs_keys (l : List (Fin S.nInt × ℤ)) (base : ℕ)
    (a : Fin S.nInt → Int) :
    (((encodeOffsetPairs S l base).flatMap (·.setsAux a)).map Prod.fst).Nodup ∧
      ∀ k : Fin S.nAux,
        k ∈ ((encodeOffsetPairs S l base).flatMap (·.setsAux a)).map Prod.fst →
          base ≤ k.val ∧ k.val < base + pairAux l.length := by
  induction l generalizing base with
  | nil => constructor <;> simp [encodeOffsetPairs]
  | cons hd rest ih =>
    obtain ⟨v, o⟩ := hd
    obtain ⟨hnd1, hr1⟩ := encodeOffsetHead_keys v o rest base a
    obtain ⟨hnd2, hr2⟩ := ih (base + rest.length)
    simp only [encodeOffsetPairs, List.flatMap_append, List.map_append, List.length_cons]
    have hpa : pairAux (rest.length + 1) = rest.length + pairAux rest.length := rfl
    refine ⟨List.Nodup.append hnd1 hnd2 ?_, ?_⟩
    · intro k hk hk'
      have h1 := (hr1 k hk).2
      have h2 := (hr2 k hk').1
      omega
    · intro k hk
      rw [List.mem_append] at hk
      rcases hk with hk | hk
      · have := hr1 k hk
        omega
      · have := hr2 k hk
        omega

/-- Block form of "owns nothing": empty keys satisfy any block. -/
theorem keys_block_of_nil {L : List (Fin S.nAux)} (h : L = []) (base cnt : ℕ) :
    L.Nodup ∧ ∀ k : Fin S.nAux, k ∈ L → base ≤ k.val ∧ k.val < base + cnt := by
  subst h; exact ⟨List.nodup_nil, by simp⟩

/-- Block form of "owns exactly its own selector". -/
theorem keys_block_of_single (base cnt : ℕ) (hcnt : 1 ≤ cnt) (hb : base < S.nAux)
    {L : List (Fin S.nAux)} (h : L = [⟨base, hb⟩]) :
    L.Nodup ∧ ∀ k : Fin S.nAux, k ∈ L → base ≤ k.val ∧ k.val < base + cnt := by
  subst h
  refine ⟨by simp, fun k hk => ?_⟩
  rw [List.mem_singleton] at hk; subst hk
  have hv : ((⟨base, hb⟩ : Fin S.nAux) : ℕ) = base := rfl
  omega

/-- Block form of "owns its own two consecutive selectors". -/
theorem keys_block_of_pair (base cnt : ℕ) (hcnt : 2 ≤ cnt)
    (hb1 : base < S.nAux) (hb2 : base + 1 < S.nAux)
    {L : List (Fin S.nAux)} (h : L = [⟨base, hb1⟩, ⟨base + 1, hb2⟩]) :
    L.Nodup ∧ ∀ k : Fin S.nAux, k ∈ L → base ≤ k.val ∧ k.val < base + cnt := by
  subst h
  refine ⟨?_, ?_⟩
  · simp [List.nodup_cons, Fin.ext_iff]
  · intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · have hv : ((⟨base, hb1⟩ : Fin S.nAux) : ℕ) = base := rfl
      omega
    · rw [List.mem_singleton] at hk; subst hk
      have hv : ((⟨base + 1, hb2⟩ : Fin S.nAux) : ℕ) = base + 1 := rfl
      omega

/-- **Owned-keys block.**  A constraint's owned selector keys are pairwise distinct and
    lie in the half-open block `[base, base + auxCount c)`.  Assignment-independent. -/
theorem encodePatternAt_keys_block (base : ℕ) (c : IntConstraint S.nInt)
    (a : Fin S.nInt → Int) :
    (((encodePatternAt S base c).flatMap (·.setsAux a)).map Prod.fst).Nodup ∧
      ∀ k : Fin S.nAux,
        k ∈ ((encodePatternAt S base c).flatMap (·.setsAux a)).map Prod.fst →
          base ≤ k.val ∧ k.val < base + auxCount c := by
  cases c
  case linear vars coeffs op target =>
    simp only [encodePatternAt]
    split
    · rw [encodeRelAt_keys]
      cases op
      case NE =>
        by_cases h : base < S.nAux
        · rw [dif_pos h]; exact keys_block_of_single base _ (Nat.le_refl 1) h rfl
        · rw [dif_neg h]; exact keys_block_of_nil rfl _ _
      all_goals exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case sum vars op target =>
    simp only [encodePatternAt]
    split
    · rw [encodeRelAt_keys]
      cases op
      case NE =>
        by_cases h : base < S.nAux
        · rw [dif_pos h]; exact keys_block_of_single base _ (Nat.le_refl 1) h rfl
        · rw [dif_neg h]; exact keys_block_of_nil rfl _ _
      all_goals exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case sum_rel_var vars op tvar =>
    simp only [encodePatternAt]
    split
    · rw [encodeRelAt_keys]
      cases op
      case NE =>
        by_cases h : base < S.nAux
        · rw [dif_pos h]; exact keys_block_of_single base _ (Nat.le_refl 1) h rfl
        · rw [dif_neg h]; exact keys_block_of_nil rfl _ _
      all_goals exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case linear_rel_var vars coeffs op tvar =>
    simp only [encodePatternAt]
    split
    · rw [encodeRelAt_keys]
      cases op
      case NE =>
        by_cases h : base < S.nAux
        · rw [dif_pos h]; exact keys_block_of_single base _ (Nat.le_refl 1) h rfl
        · rw [dif_neg h]; exact keys_block_of_nil rfl _ _
      all_goals exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case alldifferentOffset vars offsets =>
    simp only [encodePatternAt]
    split
    · rename_i hwf
      obtain ⟨hnd, hr⟩ := encodeOffsetPairs_keys ((toFinList S vars).zip offsets) base a
      refine ⟨hnd, fun k hk => ?_⟩
      have hkr := hr k hk
      have hlen : ((toFinList S vars).zip offsets).length
          = min vars.length offsets.length := by
        rw [List.length_zip]
        have hv := congrArg List.length (toFinList_val vars hwf)
        simp only [List.length_map] at hv
        rw [hv]
      have hac : auxCount (IntConstraint.alldifferentOffset vars offsets
            : IntConstraint S.nInt)
          = pairAux (min vars.length offsets.length) := rfl
      rw [hlen] at hkr
      omega
    · exact keys_block_of_nil rfl _ _
  case increasing vars =>
    simp only [encodePatternAt]
    split
    · refine keys_block_of_nil ?_ _ _
      rw [List.flatMap_eq_nil_iff.mpr (fun e he => encodeIncreasing_setsAux _ a e he),
        List.map_nil]
    · exact keys_block_of_nil rfl _ _
  case sliding_sum vars w op target =>
    simp only [encodePatternAt]
    split
    · refine keys_block_of_nil ?_ _ _
      rw [List.map_eq_nil_iff, List.flatMap_eq_nil_iff]
      intro e he
      rw [List.mem_flatMap] at he
      obtain ⟨s, _, he⟩ := he
      exact encodeRel_setsAux _ _ _ a e he
    · exact keys_block_of_nil rfl _ _
  case if_then v value nv nvalue =>
    simp only [encodePatternAt]
    split
    · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case if_then_or v value nv allowed =>
    simp only [encodePatternAt]
    split
    · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case count vars value n =>
    simp only [encodePatternAt]
    split
    · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case count_var vars value cvar =>
    simp only [encodePatternAt]
    split
    · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case modulo v n k =>
    simp only [encodePatternAt]
    split
    · refine keys_block_of_nil ?_ _ _
      rw [List.map_eq_nil_iff, List.flatMap_eq_nil_iff]
      intro e he
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp he
      rfl
    · exact keys_block_of_nil rfl _ _
  case element idx arr res =>
    simp only [encodePatternAt]
    split
    · rename_i h
      refine keys_block_of_nil ?_ _ _
      rw [List.map_eq_nil_iff, List.flatMap_eq_nil_iff]
      intro e he
      rw [List.mem_append, List.mem_append] at he
      rcases he with (he | he) | he
      · exact encodeRel_setsAux _ _ _ a e he
      · exact encodeRel_setsAux _ _ _ a e he
      · exact encodeElementCases_setsAux ⟨idx, h.1⟩ ⟨res, h.2⟩ arr 1 a e he
    · exact keys_block_of_nil rfl _ _
  case abs_diff_rel v1 v2 op t =>
    cases op
    case LE =>
      simp only [encodePatternAt]
      split
      · split
        · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    case LT =>
      simp only [encodePatternAt]
      split
      · split
        · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    case GE =>
      simp only [encodePatternAt]
      split
      · split
        · split
          · rename_i hb
            exact keys_block_of_single base _ (Nat.le_refl 1) hb rfl
          · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    case GT =>
      simp only [encodePatternAt]
      split
      · split
        · split
          · rename_i hb
            exact keys_block_of_single base _ (Nat.le_refl 1) hb rfl
          · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    case EQ =>
      simp only [encodePatternAt]
      split
      · split
        · split
          · rename_i hb
            exact keys_block_of_single base _ (Nat.le_refl 1) hb rfl
          · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    case NE =>
      simp only [encodePatternAt]
      split
      · split
        · split
          · rename_i hb
            exact keys_block_of_pair base _ (Nat.le_refl 2) (by omega) hb rfl
          · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
  case abs_diff_var v1 v2 r =>
    simp only [encodePatternAt]
    split
    · split
      · rename_i hb
        exact keys_block_of_single base _ (Nat.le_refl 1) hb rfl
      · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case maximum vars mx =>
    simp only [encodePatternAt]
    split
    · refine keys_block_of_nil ?_ _ _
      rw [List.map_eq_nil_iff, List.flatMap_eq_nil_iff]
      intro e he
      rw [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
        rfl
      · rw [List.mem_singleton] at he; subst he; rfl
    · exact keys_block_of_nil rfl _ _
  case minimum vars mn =>
    simp only [encodePatternAt]
    split
    · refine keys_block_of_nil ?_ _ _
      rw [List.map_eq_nil_iff, List.flatMap_eq_nil_iff]
      intro e he
      rw [List.mem_append] at he
      rcases he with he | he
      · obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
        rfl
      · rw [List.mem_singleton] at he; subst he; rfl
    · exact keys_block_of_nil rfl _ _
  case not_gate i o =>
    simp only [encodePatternAt]
    split
    · refine keys_block_of_nil ?_ _ _
      rw [List.flatMap_eq_nil_iff.mpr (fun e he => encodeRel_setsAux _ _ _ a e he),
        List.map_nil]
    · exact keys_block_of_nil rfl _ _
  case and_gate i1 i2 o =>
    simp only [encodePatternAt]
    split
    · split
      · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case or_gate i1 i2 o =>
    simp only [encodePatternAt]
    split
    · split
      · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case xor_gate i1 i2 o =>
    simp only [encodePatternAt]
    split
    · split
      · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case nand_gate i1 i2 o =>
    simp only [encodePatternAt]
    split
    · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case nor_gate i1 i2 o =>
    simp only [encodePatternAt]
    split
    · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case xor_all vars r =>
    rcases vars with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, _ | ⟨i4, rest⟩⟩⟩⟩
    · refine keys_block_of_nil ?_ _ _
      show ((encodePattern S (.xor_all [] r)).flatMap (·.setsAux a)).map Prod.fst = []
      rw [List.flatMap_eq_nil_iff.mpr
        (fun e he => encodePattern_setsAux (.xor_all [] r) a e he), List.map_nil]
    · refine keys_block_of_nil ?_ _ _
      show ((encodePattern S (.xor_all [i1] r)).flatMap (·.setsAux a)).map Prod.fst = []
      rw [List.flatMap_eq_nil_iff.mpr
        (fun e he => encodePattern_setsAux (.xor_all [i1] r) a e he), List.map_nil]
    · simp only [encodePatternAt]
      split
      · split
        · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    · simp only [encodePatternAt]
      split
      · split
        · exact keys_block_of_nil rfl _ _
        · exact keys_block_of_nil rfl _ _
      · exact keys_block_of_nil rfl _ _
    · refine keys_block_of_nil ?_ _ _
      show ((encodePattern S (.xor_all (i1 :: i2 :: i3 :: i4 :: rest) r)).flatMap
        (·.setsAux a)).map Prod.fst = []
      rw [List.flatMap_eq_nil_iff.mpr
        (fun e he => encodePattern_setsAux (.xor_all (i1 :: i2 :: i3 :: i4 :: rest) r) a e he),
        List.map_nil]
  case and_all vars r =>
    simp only [encodePatternAt]
    split
    · split
      · refine keys_block_of_nil ?_ _ _
        rw [List.map_eq_nil_iff, List.flatMap_eq_nil_iff]
        intro e he
        rw [List.mem_append] at he
        rcases he with he | he
        · obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
          rfl
        · rw [List.mem_singleton] at he; subst he; rfl
      · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case or_all vars r =>
    simp only [encodePatternAt]
    split
    · split
      · refine keys_block_of_nil ?_ _ _
        rw [List.map_eq_nil_iff, List.flatMap_eq_nil_iff]
        intro e he
        rw [List.mem_append] at he
        rcases he with he | he
        · obtain ⟨v, _, rfl⟩ := List.mem_map.mp he
          rfl
        · rw [List.mem_singleton] at he; subst he; rfl
      · exact keys_block_of_nil rfl _ _
    · exact keys_block_of_nil rfl _ _
  case strictLexRevLeader =>
    simp only [encodePatternAt]
    by_cases hg : ∀ i : Fin S.nInt, S.values i = [0, 1, 2]
    · rw [dif_pos hg]
      by_cases hb : base < S.nAux
      · rw [dif_pos hb]; exact keys_block_of_single base _ (Nat.le_refl 1) hb rfl
      · rw [dif_neg hb]; exact keys_block_of_nil rfl _ _
    · rw [dif_neg hg]; exact keys_block_of_nil rfl _ _
  all_goals
    refine keys_block_of_nil ?_ _ _
    simp only [encodePatternAt]
    rw [List.flatMap_eq_nil_iff.mpr (fun e he => encodePattern_setsAux _ a e he),
      List.map_nil]

/-- **Generic key distinctness** of the threaded encoding, by induction: the head
    constraint's keys are `Nodup` within its own block `[base, base + auxCount)`; the
    tail's keys all lie at or above `base + auxCount`, hence the blocks are disjoint. -/
theorem encodeConstraints_keys_nodup (cs : List (IntConstraint S.nInt)) (base : ℕ)
    (a : Fin S.nInt → Int) :
    (((encodeConstraints S cs base).flatMap (·.setsAux a)).map Prod.fst).Nodup ∧
      ∀ k : Fin S.nAux,
        k ∈ ((encodeConstraints S cs base).flatMap (·.setsAux a)).map Prod.fst →
          base ≤ k.val := by
  induction cs generalizing base with
  | nil => constructor <;> simp [encodeConstraints]
  | cons c cs ih =>
    obtain ⟨ihnd, ihlb⟩ := ih (base + auxCount c)
    obtain ⟨hnd, hrange⟩ := encodePatternAt_keys_block base c a
    simp only [encodeConstraints, List.flatMap_append, List.map_append]
    refine ⟨List.Nodup.append hnd ihnd ?_, ?_⟩
    · intro k hk hk'
      have h1 := (hrange k hk).2
      have h2 := ihlb k hk'
      omega
    · intro k hk
      rw [List.mem_append] at hk
      rcases hk with hk | hk
      · exact (hrange k hk).1
      · exact Nat.le_trans (Nat.le_add_right _ _) (ihlb k hk)

/-- The owned selector keys of the full encoding are pairwise distinct — with **no**
    hypotheses. -/
theorem encodeCSP_keys_nodup (csp : IntCSP) (a : Fin (cspSig csp).nInt → Int) :
    (((encodeCSP csp).flatMap (·.setsAux a)).map Prod.fst).Nodup :=
  (encodeConstraints_keys_nodup (S := cspSig csp) csp.constraints 0 a).1

/-- Every entry of the threaded encoding has its precondition satisfied by any solution
    (induction over the constraint list, delegating to `encodePatternAt_sound`). -/
theorem encodeConstraints_pre (cs : List (IntConstraint S.nInt)) (base : ℕ)
    (a : Fin S.nInt → Int) (hdom : ∀ i, a i ∈ S.values i)
    (hsol : ∀ c ∈ cs, patternHolds c a) :
    ∀ e ∈ encodeConstraints S cs base, e.pre a := by
  induction cs generalizing base with
  | nil => intro e he; simp [encodeConstraints] at he
  | cons c cs ih =>
    intro e he
    simp only [encodeConstraints, List.mem_append] at he
    rcases he with he | he
    · exact encodePatternAt_sound base c a hdom (hsol c (by simp)) e he
    · exact ih (base + auxCount c) (fun c' hc' => hsol c' (by simp [hc'])) e he

/-- **The general soundness theorem: CSP-SAT ⇒ PB-SAT.**  Every satisfiable `IntCSP`
    (whose every variable carries a `bound` constraint) has a *satisfiable* PB encoding:
    order-encoding any solution — with the Big-M selectors set by the generic allocator —
    satisfies the full PB formula (staircase clauses plus every constraint's encoding).
    No per-instance hypotheses: selector distinctness is `encodeCSP_keys_nodup`. -/
theorem csp_sat_pb_sat (csp : IntCSP)
    (hbound : ∀ i : Fin csp.num_vars,
        bound i (csp.extractVariableBounds i).1 (csp.extractVariableBounds i).2
          ∈ csp.constraints)
    (hsat : csp.isSatisfiableInt) :
    ∃ v : Valuation (cspSig csp),
      ∀ c ∈ (cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp), c.sat v := by
  obtain ⟨a, hsol⟩ := hsat
  -- in-domain, from the bound constraints (also feeds the gate encoders' `{0,1}` needs)
  have hdom : ∀ i, a i ∈ (cspSig csp).values i := by
    intro i
    show a i ∈ domainValues (cspLb csp i) (cspUb csp i)
    have hb : patternHolds (bound i (csp.extractVariableBounds i).1
        (csp.extractVariableBounds i).2) a := hsol _ (hbound i)
    have hb' : (csp.extractVariableBounds i).1 ≤ a i ∧
        a i ≤ (csp.extractVariableBounds i).2 := by
      simpa only [patternHolds, bound, valAt, i.is_lt, dite_true, Fin.eta] using hb
    rw [mem_domainValues]
    exact ⟨hb'.1, le_trans hb'.2 (le_max_right _ _)⟩
  -- every entry's precondition holds for the solution
  have hpre : ∀ e ∈ encodeCSP csp, e.pre a := by
    refine encodeConstraints_pre (S := cspSig csp) csp.constraints 0 a hdom ?_
    intro c hc
    exact hsol c hc
  -- the satisfying valuation: the order-encoded solution + allocator-set selectors
  refine ⟨extend a (fun _ => false)
    (globalAuxOf (encodeCSP csp) a (fun _ => false)), ?_⟩
  intro c hc
  rw [List.mem_append] at hc
  rcases hc with hmono | huser
  · exact extend_sat_monotonicity a _ _ c hmono
  · simp only [EncConstr.combine, List.mem_flatMap] at huser
    obtain ⟨e, he, hce⟩ := huser
    refine e.sound a _ _ hdom (hpre e he) ?_ c hce
    intro p hp
    have hmem : p ∈ (encodeCSP csp).flatMap (·.setsAux a) :=
      List.mem_flatMap.mpr ⟨e, he, hp⟩
    have hlk := lookup_of_nodup_mem _ p (encodeCSP_keys_nodup csp a) hmem
    simp only [globalAuxOf, hlk, Option.getD_some]

/-- **The single generic UNSAT theorem** — the contrapositive of `csp_sat_pb_sat`
    instantiated with a kernel-checked PB UNSAT certificate.  Given a `IntCSP` whose
    every variable carries a `bound` constraint (`hbound`, decided automatically) and a
    certificate over `encodeCSP csp`, the CSP is unsatisfiable.  No other per-instance
    obligation. -/
theorem csp_unsat (csp : IntCSP)
    (cert : VeriPB.Reflect.formulaUnsat
      (((cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)).toArray.map
        PBConstr.toNatConstr))
    (hbound : ∀ i : Fin csp.num_vars,
        bound i (csp.extractVariableBounds i).1 (csp.extractVariableBounds i).2
          ∈ csp.constraints := by decide) :
    ¬ csp.isSatisfiableInt := by
  intro hsat
  obtain ⟨v, hv⟩ := csp_sat_pb_sat csp hbound hsat
  obtain ⟨c, hc, hnc⟩ := unsat_bridge
    ((cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)).toArray cert v
  rw [List.toList_toArray] at hc
  exact hnc (hv c hc)

open Lean Lean.Meta Lean.Elab Lean.Elab.Term in
/-- The elaborator behind `csp_unsat_file`.  It discharges PBLean's reflection check with a
    hand-built `Lean.ofReduceBool` proof term (PBLean's `veripb_reflect` style) — an
    `addAndCompile`d `Bool` aux (`checkProofBool cs numVars cert`) plus `ofReduceBool` and
    `checkProof_sound` — instead of the `native_decide` *tactic*, so every committed UNSAT
    theorem carries the single stable `Lean.ofReduceBool` axiom rather than a fresh
    per-theorem `._native.native_decide.ax`.  The auxiliary + cert declarations are named
    after the enclosing theorem; the certificate string is spliced by `include_str`
    (module-relative, compile time). -/
elab "cspUnsatReflect " cspStx:term:max numVarsStx:term:max certStx:term:max : term => do
  let certE ← instantiateMVars (← elabTerm certStx (some (Lean.mkConst ``String)))
  let csE ← instantiateMVars (← elabTerm
    (← `((((cspSig $cspStx).monotonicity ++ EncConstr.combine (encodeCSP $cspStx)).toArray.map
          PBConstr.toNatConstr)))
    (some (mkApp (Lean.mkConst ``Array [.zero]) (Lean.mkConst ``Sat.PB.Constr))))
  let numE ← instantiateMVars (← elabTerm numVarsStx (some (Lean.mkConst ``Nat)))
  let baseName ← match (← getDeclName?) with
    | some n => pure n
    | none => mkFreshUserName `_cspUnsat
  let certName := baseName ++ `cert
  let auxName := certName ++ `check
  addAndCompile <| .defnDecl {
    name := auxName, levelParams := [], type := Lean.mkConst ``Bool
    value := mkApp3 (Lean.mkConst ``VeriPB.Reflect.checkProofBool) csE numE certE
    hints := .abbrev, safety := .safe }
  let auxConst := Lean.mkConst auxName
  let hEqTrue := mkApp3 (Lean.mkConst ``Lean.ofReduceBool) auxConst (Lean.mkConst ``Bool.true)
    (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Bool)
      (mkApp (Lean.mkConst ``Lean.reduceBool) auxConst))
  addDecl <| Declaration.thmDecl {
    name := certName, levelParams := []
    type := mkApp (Lean.mkConst ``VeriPB.Reflect.formulaUnsat) csE
    value := mkApp4 (Lean.mkConst ``VeriPB.Reflect.checkProof_sound) csE numE certE hEqTrue }
  elabTerm (← `(csp_unsat $cspStx $(mkIdent certName))) none

/-- **File-based generic UNSAT.**  `csp_unsat_file csp numVars "certs/foo.pbp"` is
    `csp_unsat csp cert` with the VeriPB kernel proof loaded from a committed file at
    compile time (`include_str`) and re-checked by PBLean's reflection checker.  The
    reflection step is discharged via a hand-built `Lean.ofReduceBool` term (see
    `cspUnsatReflect`), so the theorem's only extra axiom is `Lean.ofReduceBool`.  The
    formula is inferred from `csp`; `numVars` is the OPB `#variable=` count
    (`Σ (cspSig csp).width + nBool + nAux` — the Big-M selectors count too; printed by
    `experiments/gen_cert.py`). -/
macro "csp_unsat_file " csp:term:max numVars:term:max path:str : term =>
  `(cspUnsatReflect $csp $numVars (include_str $path))

end CSP.L2S.PB
