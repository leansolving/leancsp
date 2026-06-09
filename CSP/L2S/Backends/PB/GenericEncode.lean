import CSP.L2S.Backends.PB.Library

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

/-- The order-encoding signature derived from `csp`'s bounds. -/
def cspSig (csp : IntCSP) : CSPSig :=
  toCSPSig csp (cspLb csp) (cspUb csp) (cspLb_le_cspUb csp)

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

/-- The value list used for `alldifferent`/`ne` encodings: the union of the variables'
    domains. -/
def domOf (S : CSPSig) (vars : List (Fin S.nInt)) : List Int :=
  (vars.flatMap (fun i => S.values i)).dedup

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
  | _ => []

/-- Every entry `encodePattern` emits is aux-free. -/
theorem encodePattern_setsAux (c : IntConstraint S.nInt) (a : Fin S.nInt → Int)
    (e : EncConstr S) (he : e ∈ encodePattern S c) : e.setsAux a = [] := by
  cases c
  case alldifferent vars => simp only [encodePattern] at he; split at he <;> simp_all [encAllDifferent]
  case ne v1 v2 => simp only [encodePattern] at he; split at he <;> simp_all [encNotEqual]
  case eq_const v c => simp only [encodePattern] at he; split at he <;> simp_all [encEqConst]
  case ne_const v c => simp only [encodePattern] at he; split at he <;> simp_all [encNeConst]
  case at_most_k vars k => simp only [encodePattern] at he; split at he <;> simp_all [encAtMostK]
  case at_least_k vars k => simp only [encodePattern] at he; split at he <;> simp_all [encAtLeastK]
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
  all_goals (simp only [encodePattern] at he; exact absurd he (by simp))

/-! ### The combined encoding and the generic theorem -/

/-- The full PB constraint set of `csp`: the order-encoding staircase plus every
    constraint's encoding. -/
def encodeCSP (csp : IntCSP) : List (EncConstr (cspSig csp)) :=
  csp.constraints.flatMap (encodePattern (cspSig csp))

/-- **The single generic UNSAT theorem.**  Given a `IntCSP` whose every variable carries
    a `bound` constraint (`hbound`, decided automatically) and a kernel-checked PB UNSAT
    certificate over `encodeCSP csp`, the CSP is unsatisfiable — with no per-instance
    soundness proof. -/
theorem csp_unsat (csp : IntCSP)
    (cert : VeriPB.Reflect.formulaUnsat
      (((cspSig csp).monotonicity ++ EncConstr.combine (encodeCSP csp)).toArray.map
        PBConstr.toNatConstr))
    (hbound : ∀ i : Fin csp.num_vars,
        bound i (csp.extractVariableBounds i).1 (csp.extractVariableBounds i).2
          ∈ csp.constraints := by decide) :
    ¬ csp.isSatisfiableInt := by
  rintro ⟨a, hsol⟩
  have hfree : ∀ a', ∀ e ∈ encodeCSP csp, e.setsAux a' = [] := by
    intro a' e he
    simp only [encodeCSP, List.mem_flatMap] at he
    obtain ⟨c, _, hce⟩ := he
    exact encodePattern_setsAux c a' e hce
  refine csp_unsat_of_encfree (cspSig csp) (encodeCSP csp) hfree cert ⟨a, ?_, ?_⟩
  · -- in-domain, from the bound constraints
    intro i
    show a i ∈ domainValues (cspLb csp i) (cspUb csp i)
    have hb : patternHolds (bound i (csp.extractVariableBounds i).1
        (csp.extractVariableBounds i).2) a := hsol _ (hbound i)
    have hb' : (csp.extractVariableBounds i).1 ≤ a i ∧
        a i ≤ (csp.extractVariableBounds i).2 := by
      simpa only [patternHolds, bound, valAt, i.is_lt, dite_true, Fin.eta] using hb
    rw [mem_domainValues]
    exact ⟨hb'.1, le_trans hb'.2 (le_max_right _ _)⟩
  · -- every encoded constraint's precondition holds for the solution
    intro e he
    simp only [encodeCSP, List.mem_flatMap] at he
    obtain ⟨c, hc, hce⟩ := he
    exact encodePattern_sound c a (hsol c hc) e hce

end CSP.L2S.PB
