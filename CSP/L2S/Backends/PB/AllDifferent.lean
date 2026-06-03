import CSP.L2S.Backends.PB.Semantics

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

The PB-constraint *assembly* on top (per-value `≤ 1` constraints + the
distinctness → at-most-one argument) builds on these.
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

end CSP.L2S.PB
