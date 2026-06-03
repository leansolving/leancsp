import CSP.L2S.Backends.PB.Semantics
import CSP.L2S.Backends.PB.SignedPB

namespace CSP.L2S.PB

open CSPSig

/-!
# PB backend — `alldifferent` value-indicator semantics (PLAN.md §6.5)

`alldifferent` over finite-domain integer variables decomposes, value by value,
into `∀ v ∈ ⋃ᵢ domainᵢ : Σⱼ [xⱼ = v] ≤ 1`.  The order-encoded indicator
`[xⱼ = v] = ⟦xⱼ ≤ v⟧ − ⟦xⱼ ≤ v − 1⟧` is built from the smart threshold
constructor `mkLeLit`.  This file proves the reusable semantic core:

* `mkLeLit_eval` — under order consistency, `⟦xⱼ ≤ k⟧` (as built by `mkLeLit`)
  evaluates to the indicator `[intValue j ≤ k]`.  This is the order-encoding's
  *threshold faithfulness*, and is reused by every value-based encoding
  (`alldifferent`, hard `≠`, reified `≠`).
* `eqIndicator_eval` — hence the difference indicator evaluates to
  `[intValue j = v]` for any value `v`.

The PB-constraint *assembly* follows in the second half: `litConstContrib` folds
each variable's `mkLeLit` indicators into signed terms + a constant, `perValueConstr`
builds the `Σⱼ [xⱼ = v] ≤ 1` constraint per value, and `encodeAllDifferent` /
`encodeAllDifferent_sound` close the loop — pairwise-distinct recovered values
(`Nodup`) satisfy every per-value constraint.
-/

variable {S : CSPSig}

/-- Evaluate a `LitConst` (literal-or-constant) under a valuation, as an `Int`. -/
def evalLitConst {V : Type} (v : V → Bool) : LitConst V → Int
  | .lit ℓ   => (evalLit v ℓ : Int)
  | .const b => if b then 1 else 0

/-- **Threshold faithfulness of the order encoding.** Under order consistency, the
    smart threshold literal `mkLeLit i k` (denoting `xᵢ ≤ k`) evaluates to the
    indicator `[intValue i ≤ k]`.  Boundary cases (`k` below the minimum / at-or-above
    the maximum) are handled by `mkLeLit`'s constant collapse. -/
theorem mkLeLit_eval (v : Valuation S) (hv : v.orderConsistent) (i : Fin S.nInt) (k : Int) :
    evalLitConst v (LitConst.mkLeLit S i k) = if v.intValue i ≤ k then (1 : Int) else 0 := by
  obtain ⟨M, hMw, hval, hbits⟩ := intValue_switch i v hv
  have hmem : v.intValue i ∈ S.values i := Valuation.intValue_mem_values v hv i
  have hwd : S.width i = (S.values i).length - 1 := rfl
  -- `nth` is monotone on in-range indices, and bridges to `getElem`.
  have nth_mono : ∀ {p q : ℕ}, p ≤ q → q < (S.values i).length → S.nth i p ≤ S.nth i q := by
    intro p q hpq hq
    rcases eq_or_lt_of_le hpq with rfl | hlt
    · exact le_refl _
    · have hp : p < (S.values i).length := lt_trans hlt hq
      show (S.values i).getD p 0 ≤ (S.values i).getD q 0
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      exact le_of_lt ((List.pairwise_iff_getElem.mp (S.sorted i)) p q hp hq hlt)
  have nth_get : ∀ {m : ℕ} (h : m < (S.values i).length), S.nth i m = (S.values i)[m]'h := by
    intro m h
    show (S.values i).getD m 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl
  unfold LitConst.mkLeLit
  cases hf : (S.values i).findIdx? (· > k) with
  | none =>
    -- every domain value is ≤ k, so in particular `intValue i ≤ k`.
    rw [List.findIdx?_eq_none_iff] at hf
    have hle : v.intValue i ≤ k := by
      have hx := hf _ hmem
      simp only [decide_eq_false_iff_not, not_lt] at hx
      exact hx
    simp [evalLitConst, hle]
  | some n =>
    obtain ⟨hnlen, hpn, hbefore⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [decide_eq_true_eq] at hpn
    cases n with
    | zero =>
      -- the smallest domain value already exceeds `k`, so `intValue i > k`.
      have hmin : S.nth i 0 ≤ v.intValue i := by
        obtain ⟨t, htlen, hteq⟩ := List.getElem_of_mem hmem
        rw [← hteq, ← nth_get htlen]
        exact nth_mono (Nat.zero_le t) htlen
      have h0k : k < S.nth i 0 := by rw [nth_get hnlen]; exact hpn
      have hnle : ¬ v.intValue i ≤ k := by omega
      simp [evalLitConst, hnle]
    | succ j =>
      -- `values[j] ≤ k < values[j+1]`: `mkLeLit` is `thr i ⟨j, _⟩`, and
      -- `intValue i ≤ k ↔ M ≤ j ↔ thr i j`.
      have hjlt : j < S.width i := by omega
      -- reduce the (iota) match on `some (j+1)`, then resolve the in-range `dite`.
      show evalLitConst v (dite (j < S.width i)
            (fun hj => LitConst.lit (Lit.pos (PBVar.thr i ⟨j, hj⟩)))
            (fun _ => LitConst.const true))
          = if v.intValue i ≤ k then (1 : Int) else 0
      rw [dif_pos hjlt]
      have hjk : S.nth i j ≤ k := by
        have hb := hbefore j (Nat.lt_succ_self j)
        simp only [decide_eq_true_eq, not_lt] at hb
        rw [nth_get (by omega)]; exact hb
      have hk1 : k < S.nth i (j + 1) := by rw [nth_get hnlen]; exact hpn
      have hiff : (v.intValue i ≤ k) ↔ (M ≤ j) := by
        rw [hval]
        constructor
        · intro h
          by_contra hMj
          rw [not_le] at hMj
          have : S.nth i (j + 1) ≤ S.nth i M := nth_mono hMj (by omega)
          omega
        · intro h
          have : S.nth i M ≤ S.nth i j := nth_mono h (by omega)
          omega
      have hthr : v (.thr i ⟨j, hjlt⟩) = decide (M ≤ j) := hbits ⟨j, hjlt⟩
      by_cases hMj : M ≤ j <;>
        simp [evalLitConst, evalLit, hthr, hiff, hMj]

/-- The order-encoded equality indicator `[xⱼ = v] = ⟦xⱼ ≤ v⟧ − ⟦xⱼ ≤ v − 1⟧`. -/
def eqIndicator (v : Valuation S) (i : Fin S.nInt) (val : Int) : Int :=
  evalLitConst v (LitConst.mkLeLit S i val) - evalLitConst v (LitConst.mkLeLit S i (val - 1))

/-- **Indicator soundness.** Under order consistency, the equality indicator is
    `1` exactly when `intValue i = val`, else `0`. -/
theorem eqIndicator_eval (v : Valuation S) (hv : v.orderConsistent) (i : Fin S.nInt) (val : Int) :
    eqIndicator v i val = if v.intValue i = val then 1 else 0 := by
  unfold eqIndicator
  rw [mkLeLit_eval v hv i val, mkLeLit_eval v hv i (val - 1)]
  by_cases h : v.intValue i = val
  · rw [if_pos h]
    have h1 : v.intValue i ≤ val := by omega
    have h2 : ¬ v.intValue i ≤ val - 1 := by omega
    rw [if_pos h1, if_neg h2]; ring
  · rw [if_neg h]
    by_cases h1 : v.intValue i ≤ val
    · have h2 : v.intValue i ≤ val - 1 := by omega
      rw [if_pos h1, if_pos h2]; ring
    · have h2 : ¬ v.intValue i ≤ val - 1 := by omega
      rw [if_neg h1, if_neg h2]; ring

/-! ### Per-value constraints and the `alldifferent` encoder (common domain, PLAN §6.5)

The PB-constraint assembly: each value `val` in the (shared) domain gets the
constraint `Σⱼ [xⱼ = val] ≤ 1`, encoded in signed `≥` form by folding each
variable's two `mkLeLit` indicators into weighted terms + a constant
(`litConstContrib` absorbs the boundary constants `mkLeLit` produces).  Soundness
rides on `eqIndicator_eval` plus a `Nodup`-of-recovered-values → at-most-one
counting argument.
-/

variable {V : Type}

/-- Signed PB terms (+ folded constant) for `a · ⟦lc⟧`: a literal yields a weighted
    term; a Boolean constant collapses into the standalone constant. -/
def litConstContrib (a : Int) : LitConst V → List (Int × Lit V) × Int
  | .lit ℓ   => ([(a, ℓ)], 0)
  | .const b => ([], if b then a else 0)

theorem litConstContrib_eval (v : V → Bool) (a : Int) (lc : LitConst V) :
    signedEval v (litConstContrib a lc).1 + (litConstContrib a lc).2 = a * evalLitConst v lc := by
  cases lc with
  | lit ℓ   => simp [litConstContrib, signedEval, evalLitConst]
  | const b => cases b <;> simp [litConstContrib, signedEval, evalLitConst]

-- A local copy of `Encode.signedEval_append`, re-proved here to keep this file's
-- imports at `{Semantics, SignedPB}` (importing `Encode` would pull in `Substitution`).
private theorem signedEval_append (v : V → Bool) (a b : List (Int × Lit V)) :
    signedEval v (a ++ b) = signedEval v a + signedEval v b := by
  simp [signedEval, List.sum_append]

/-- A `Nodup` integer list has at most one element equal to any given value, so the
    `[· = val]` indicator sum is `≤ 1`. -/
theorem nodup_indicator_sum_le_one (L : List Int) (val : Int) (hd : L.Nodup) :
    (L.map (fun x => if x = val then (1 : Int) else 0)).sum ≤ 1 := by
  induction L with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hd
    obtain ⟨ha, hdt⟩ := hd
    simp only [List.map_cons, List.sum_cons]
    by_cases h : a = val
    · subst h
      have htail : (t.map (fun x => if x = a then (1 : Int) else 0)).sum = 0 := by
        have hz : t.map (fun x => if x = a then (1 : Int) else 0) = t.map (fun _ => (0 : Int)) := by
          apply List.map_congr_left
          intro x hx
          rw [if_neg (by rintro rfl; exact ha hx)]
        rw [hz]; simp
      rw [if_pos rfl, htail]; omega
    · rw [if_neg h]; simpa using ih hdt

/-- Per-variable contribution to `Σⱼ −[xⱼ = val]` (signed terms + folded constant),
    from the two order-encoding thresholds `⟦xⱼ ≤ val⟧` and `⟦xⱼ ≤ val−1⟧`. -/
def adContrib (j : Fin S.nInt) (val : Int) : List (Int × Lit (PBVar S)) × Int :=
  ((litConstContrib (1 : Int) (LitConst.mkLeLit S j (val - 1))).1 ++
     (litConstContrib (-1 : Int) (LitConst.mkLeLit S j val)).1,
   (litConstContrib (1 : Int) (LitConst.mkLeLit S j (val - 1))).2 +
     (litConstContrib (-1 : Int) (LitConst.mkLeLit S j val)).2)

/-- Under order consistency, the per-variable contribution evaluates to `−[intValue j = val]`. -/
theorem adContrib_eval (v : Valuation S) (hv : v.orderConsistent) (j : Fin S.nInt) (val : Int) :
    signedEval v (adContrib j val).1 + (adContrib j val).2
      = -(if v.intValue j = val then (1 : Int) else 0) := by
  simp only [adContrib]
  rw [signedEval_append]
  have hlo := litConstContrib_eval v (1 : Int) (LitConst.mkLeLit S j (val - 1))
  have hhi := litConstContrib_eval v (-1 : Int) (LitConst.mkLeLit S j val)
  have heq := eqIndicator_eval v hv j val
  unfold eqIndicator at heq
  linarith [hlo, hhi, heq]

/-- The per-value cardinality constraint `Σⱼ [xⱼ = val] ≤ k`, in signed-PB `≥`
    form.  `alldifferent` uses `k = 1` (`perValueConstr` below); multi-valued
    not-all-equal uses `k = |vars| − 1`. -/
def perValueConstrLe (vars : List (Fin S.nInt)) (val : Int) (k : Int) :
    SignedPBConstr (PBVar S) where
  terms := (vars.map (fun j => adContrib j val)).flatMap Prod.fst
  rhs := -k - ((vars.map (fun j => adContrib j val)).map Prod.snd).sum

/-- The folded terms + constant of a per-value constraint sum to `−Σⱼ [intValue j = val]`. -/
private theorem perValueConstrLe_key (v : Valuation S) (hv : v.orderConsistent)
    (vars : List (Fin S.nInt)) (val : Int) :
    signedEval v ((vars.map (fun j => adContrib j val)).flatMap Prod.fst)
      + ((vars.map (fun j => adContrib j val)).map Prod.snd).sum
      = -((vars.map (fun j => if v.intValue j = val then (1 : Int) else 0)).sum) := by
  induction vars with
  | nil => simp [signedEval]
  | cons j t ih =>
    simp only [List.map_cons, List.flatMap_cons, List.sum_cons]
    rw [signedEval_append]
    have hj := adContrib_eval v hv j val
    linarith [hj, ih]

/-- **Per-value soundness.** If at most `k` variables recover the value `val`
    (`Σⱼ [intValue j = val] ≤ k`), the per-value constraint holds. -/
theorem perValueConstrLe_sound (v : Valuation S) (hv : v.orderConsistent)
    (vars : List (Fin S.nInt)) (val : Int) (k : Int)
    (h1 : (vars.map (fun j => if v.intValue j = val then (1 : Int) else 0)).sum ≤ k) :
    (perValueConstrLe vars val k).sat v := by
  have hkey := perValueConstrLe_key v hv vars val
  simp only [SignedPBConstr.sat, perValueConstrLe]
  linarith [hkey, h1]

/-- The `alldifferent` per-value constraint `Σⱼ [xⱼ = val] ≤ 1` (the `k = 1` case). -/
def perValueConstr (vars : List (Fin S.nInt)) (val : Int) : SignedPBConstr (PBVar S) :=
  perValueConstrLe vars val 1

/-- **Per-value soundness (`alldifferent`).** If at most one variable's recovered
    value is `val` (`Σⱼ [intValue j = val] ≤ 1`), the per-value constraint holds. -/
theorem perValueConstr_sound (v : Valuation S) (hv : v.orderConsistent)
    (vars : List (Fin S.nInt)) (val : Int)
    (h1 : (vars.map (fun j => if v.intValue j = val then (1 : Int) else 0)).sum ≤ 1) :
    (perValueConstr vars val).sat v :=
  perValueConstrLe_sound v hv vars val 1 h1

/-- The `alldifferent` encoding over a value list `D` (the union of the variables'
    domains): one `Σⱼ [xⱼ = val] ≤ 1` constraint per value. -/
def encodeAllDifferent (vars : List (Fin S.nInt)) (D : List Int) :
    List (SignedPBConstr (PBVar S)) :=
  D.map (perValueConstr vars)

/-- **`alldifferent` soundness.** If the variables' recovered values are pairwise
    distinct (`Nodup`), every per-value constraint of the encoding holds. -/
theorem encodeAllDifferent_sound (v : Valuation S) (hv : v.orderConsistent)
    (vars : List (Fin S.nInt)) (D : List Int)
    (hd : (vars.map v.intValue).Nodup) :
    ∀ c ∈ encodeAllDifferent vars D, c.sat v := by
  intro c hc
  simp only [encodeAllDifferent, List.mem_map] at hc
  obtain ⟨val, _, rfl⟩ := hc
  have hcount := nodup_indicator_sum_le_one (vars.map v.intValue) val hd
  rw [List.map_map] at hcount
  exact perValueConstr_sound v hv vars val hcount

/-! ### Multi-valued not-all-equal (PLAN §6.8, the k>2-colour case)

`schur_triple` and its k-ary generalization over a domain `{1..k}` with `k > 2`
(3-colour Schur, …) cannot use the binary bottom-threshold reduction of
`NotAllEqual.lean`.  But not-all-equal is exactly a **per-value cardinality**
statement, reusing the `alldifferent` machinery with a relaxed bound:

  `x₁,…,x_m` are not all equal  ⟺  ∀ val : at most `m−1` of them equal `val`
                                ⟺  ∀ val : `Σⱼ [xⱼ = val] ≤ m − 1`.

(⟸: if all equalled some `w`, the `val = w` constraint would force `m ≤ m−1`.
⟹: if all `m` equalled a fixed `val` they would be all equal.)  This is aux-free
— no reified disequality is needed — so, like `alldifferent`, it rides on the
generic spine through `extend_intValue`.
-/

/-- Each `[· = val]` indicator is `≤ 1`, so a length-`n` list has indicator sum
    `≤ n`. -/
private theorem indicator_sum_le_length (L : List Int) (val : Int) :
    (L.map (fun x => if x = val then (1 : Int) else 0)).sum ≤ (L.length : Int) := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have h1 : (if a = val then (1 : Int) else 0) ≤ 1 := by split <;> norm_num
    linarith

/-- If some element of `L` differs from `val`, at most `|L| − 1` elements equal
    `val`. -/
private theorem indicator_sum_le_length_sub_one (L : List Int) (val : Int)
    (h : ∃ x ∈ L, x ≠ val) :
    (L.map (fun x => if x = val then (1 : Int) else 0)).sum ≤ (L.length : Int) - 1 := by
  induction L with
  | nil => obtain ⟨x, hx, _⟩ := h; simp at hx
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    by_cases ha : a = val
    · -- `a` equals `val`; the differing witness lies in the tail.
      rw [if_pos ha]
      have ht : ∃ x ∈ t, x ≠ val := by
        obtain ⟨x, hx, hxv⟩ := h
        rcases List.mem_cons.mp hx with rfl | hx_t
        · exact absurd ha hxv
        · exact ⟨x, hx_t, hxv⟩
      linarith [ih ht]
    · rw [if_neg ha]; linarith [indicator_sum_le_length t val]

/-- The multi-valued not-all-equal encoding over a value list `D` (the shared
    domain): one `Σⱼ [xⱼ = val] ≤ |vars| − 1` constraint per value. -/
def encodeNotAllEqualMulti (vars : List (Fin S.nInt)) (D : List Int) :
    List (SignedPBConstr (PBVar S)) :=
  D.map (fun val => perValueConstrLe vars val ((vars.length : Int) - 1))

/-- **Multi-valued not-all-equal soundness.** If two of the variables' recovered
    values differ (the tuple is not all equal), every per-value constraint of the
    encoding holds: for each `val`, one of the two differing values is `≠ val`, so
    at most `|vars| − 1` variables recover `val`. -/
theorem encodeNotAllEqualMulti_sound (v : Valuation S) (hv : v.orderConsistent)
    (vars : List (Fin S.nInt)) (D : List Int)
    (hne : ∃ i ∈ vars, ∃ i' ∈ vars, v.intValue i ≠ v.intValue i') :
    ∀ c ∈ encodeNotAllEqualMulti vars D, c.sat v := by
  intro c hc
  simp only [encodeNotAllEqualMulti, List.mem_map] at hc
  obtain ⟨val, _, rfl⟩ := hc
  apply perValueConstrLe_sound v hv vars val _
  -- Reduce the `Fin`-indexed indicator sum to one over `vars.map v.intValue`.
  have key := indicator_sum_le_length_sub_one (vars.map v.intValue) val ?_
  · rw [List.map_map, List.length_map] at key; exact key
  · -- Some recovered value differs from `val`: one of the two differing values.
    obtain ⟨i, hi, i', hi', hii⟩ := hne
    by_cases h : v.intValue i = val
    · exact ⟨v.intValue i', List.mem_map.mpr ⟨i', hi', rfl⟩, fun hc => hii (h.trans hc.symm)⟩
    · exact ⟨v.intValue i, List.mem_map.mpr ⟨i, hi, rfl⟩, h⟩

/-! ### `xⱼ ≠ val` — the aux-free `≠` special case (PLAN §6.4)

The general linear `Σ aᵢ xᵢ ≠ b` needs a fresh selector variable (Big-M), but the
common `xⱼ ≠ val` (variable ≠ constant) case is aux-free: it is exactly
`[xⱼ = val] ≤ 0`, i.e. `−[xⱼ = val] ≥ 0`, reusing the per-variable indicator
`adContrib`.  (The `xᵢ ≠ xⱼ` case is `encodeAllDifferent [i, j] _`.)
-/

/-- Encode `xⱼ ≠ val` (variable ≠ constant) as `−[xⱼ = val] ≥ 0`. -/
def encodeNeConst (j : Fin S.nInt) (val : Int) : SignedPBConstr (PBVar S) where
  terms := (adContrib j val).1
  rhs := -(adContrib j val).2

/-- **Soundness.** If the recovered value of `xⱼ` is not `val`, the constraint holds. -/
theorem encodeNeConst_sound (v : Valuation S) (hv : v.orderConsistent)
    (j : Fin S.nInt) (val : Int) (h : v.intValue j ≠ val) :
    (encodeNeConst j val).sat v := by
  have he := adContrib_eval v hv j val
  rw [if_neg h] at he
  simp only [SignedPBConstr.sat, encodeNeConst]
  linarith [he]

/-! ### Unit test: two variables over `{0,1}` with distinct values -/

namespace AllDifferentTest

/-- Two integer variables, shared binary domain `{0, 1}`. -/
def sigAD : CSPSig where
  nInt := 2
  nBool := 0
  nAux := 0
  values := fun _ => [0, 1]
  sorted := by intro _; decide
  nonempty := by intro _; decide

/-- The valuation `x₀ = 0` (its `≤ 0` threshold set), `x₁ = 1` (threshold unset). -/
def vAD : Valuation sigAD
  | .thr i _ => decide (i.val = 0)
  | _        => false

/-- The two variables (raw `Fin.mk` dodges the projection-`OfNat` friction, MEM_002 #12). -/
def varsAD : List (Fin sigAD.nInt) := [⟨0, by decide⟩, ⟨1, by decide⟩]

/-- `vAD` is order-consistent (each variable has a single threshold, so the
    adjacency premise is vacuous). -/
theorem vAD_orderConsistent : vAD.orderConsistent := by
  intro i j j' hj' _
  have hw : sigAD.width i = 1 := rfl
  have := j.isLt; have := j'.isLt; omega

-- The recovered values are `0` and `1` — distinct, so `alldifferent` holds.
example : vAD.intValue ⟨0, by decide⟩ = 0 ∧ vAD.intValue ⟨1, by decide⟩ = 1 := by decide

example : ∀ c ∈ encodeAllDifferent varsAD [0, 1], c.sat vAD :=
  encodeAllDifferent_sound vAD vAD_orderConsistent varsAD [0, 1] (by decide)

end AllDifferentTest

end CSP.L2S.PB
