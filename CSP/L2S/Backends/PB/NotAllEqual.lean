import CSP.L2S.Backends.PB.SignedPB
import CSP.L2S.Backends.PB.Semantics

namespace CSP.L2S.PB

open scoped BigOperators

/-!
# PB backend — the not-all-equal encoder (binary domains)

`schur_triple` and its k-ary generalization say a tuple of variables is **not all
equal** — the pattern behind the Schur / van der Waerden / Ramsey instances.
Over a list of literals this is "not all the same bit", encoded as two clauses:

* `Σ ⟦ℓᵢ⟧ ≥ 1` — at least one literal is true, and
* `Σ ⟦¬ℓᵢ⟧ ≥ 1` — at least one literal is false.

`encodeNotAllEqual` is the reusable core.  For binary integer variables (a shared
two-element domain) `intValue_binary` shows the bottom threshold bit recovers the
value, and `encodeNotAllEqualBin_sound` lifts the core soundness to the recovered
values.  The `k > 2`-valued case is `encodeNotAllEqualMulti` in `AllDifferent.lean`.
-/

/-! ## The general literal-level primitive (over any variable type) -/

variable {V : Type}

/-- A nonnegative integer list has a nonnegative sum. -/
private theorem list_sum_nonneg :
    ∀ (L : List Int), (∀ x ∈ L, (0 : Int) ≤ x) → (0 : Int) ≤ L.sum
  | [],     _   => by simp
  | a :: t, hnn => by
    rw [List.sum_cons]
    have ht := list_sum_nonneg t (fun x hx => hnn x (List.mem_cons.mpr (Or.inr hx)))
    have ha := hnn a (List.mem_cons.mpr (Or.inl rfl))
    linarith

/-- A nonnegative integer list containing `1` sums to at least `1`. -/
private theorem one_le_sum_of_mem_of_nonneg :
    ∀ (L : List Int), (1 : Int) ∈ L → (∀ x ∈ L, (0 : Int) ≤ x) → (1 : Int) ≤ L.sum
  | [],     hmem, _   => by simp at hmem
  | a :: t, hmem, hnn => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · have ht : (0 : Int) ≤ t.sum :=
        list_sum_nonneg t (fun x hx => hnn x (List.mem_cons.mpr (Or.inr hx)))
      linarith
    · have ha : (0 : Int) ≤ a := hnn a (List.mem_cons.mpr (Or.inl rfl))
      have ih : (1 : Int) ≤ t.sum :=
        one_le_sum_of_mem_of_nonneg t hmem' (fun x hx => hnn x (List.mem_cons.mpr (Or.inr hx)))
      linarith

/-- Encode "the literals `ℓᵢ` are not all equal (as bits)" as two PB clauses:
    at least one literal true (`Σ ⟦ℓᵢ⟧ ≥ 1`) and at least one false
    (`Σ ⟦¬ℓᵢ⟧ ≥ 1`). -/
def encodeNotAllEqual (lits : List (Lit V)) : List (SignedPBConstr V) :=
  [ { terms := lits.map (fun ℓ => ((1 : Int), ℓ)),        rhs := 1 },
    { terms := lits.map (fun ℓ => ((1 : Int), ℓ.negate)), rhs := 1 } ]

/-- If some literal in `lits.map (·, f ·)` evaluates to `1`, the (all-`1`-coefficient)
    signed sum is `≥ 1`: every term is `≥ 0` and one of them is `1`. -/
theorem signedEval_lits_ge_one (v : V → Bool) (lits : List (Lit V)) (f : Lit V → Lit V)
    (h : ∃ ℓ ∈ lits, evalLit v (f ℓ) = 1) :
    (1 : Int) ≤ signedEval v (lits.map (fun ℓ => ((1 : Int), f ℓ))) := by
  have hrw : signedEval v (lits.map (fun ℓ => ((1 : Int), f ℓ)))
      = (lits.map (fun ℓ => (evalLit v (f ℓ) : Int))).sum := by
    simp only [signedEval, List.map_map, Function.comp_def, one_mul]
  rw [hrw]
  obtain ⟨ℓ, hℓmem, hℓ⟩ := h
  have hmem : (1 : Int) ∈ lits.map (fun ℓ => (evalLit v (f ℓ) : Int)) := by
    rw [List.mem_map]; exact ⟨ℓ, hℓmem, by simp [hℓ]⟩
  have hnn : ∀ x ∈ lits.map (fun ℓ => (evalLit v (f ℓ) : Int)), (0 : Int) ≤ x := by
    intro x hx; rw [List.mem_map] at hx; obtain ⟨ℓ', _, rfl⟩ := hx; exact Nat.cast_nonneg _
  exact one_le_sum_of_mem_of_nonneg _ hmem hnn

/-- **Soundness of the literal primitive.** If some literal is true and some
    literal is false (i.e. the literals are not all equal as bits), then both
    encoded clauses are satisfied. -/
theorem encodeNotAllEqual_sound (v : V → Bool) (lits : List (Lit V))
    (hT : ∃ ℓ ∈ lits, evalLit v ℓ = 1)
    (hF : ∃ ℓ ∈ lits, evalLit v ℓ = 0) :
    ∀ c ∈ encodeNotAllEqual lits, c.sat v := by
  intro c hc
  simp only [encodeNotAllEqual, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · -- at least one true: use `f = id`.
    show (1 : Int) ≤ signedEval v _
    exact signedEval_lits_ge_one v lits id hT
  · -- at least one false: `f = negate`, and a false literal has a true negation.
    show (1 : Int) ≤ signedEval v _
    refine signedEval_lits_ge_one v lits Lit.negate ?_
    obtain ⟨ℓ, hmem, h0⟩ := hF
    exact ⟨ℓ, hmem, by have := evalLit_negate_add v ℓ; omega⟩

/-! ## CSP binary integer variables -/

section
variable {S : CSPSig}
open CSPSig

/-- For a binary integer variable (domain exactly `[c0, c1]`), the recovered value
    is determined by its single (bottom) threshold bit: `c0` if set, else `c1`. -/
theorem intValue_binary (v : Valuation S) (i : Fin S.nInt) (c0 c1 : Int)
    (h : S.values i = [c0, c1]) (hw : 0 < S.width i) :
    v.intValue i = if v (.thr i ⟨0, hw⟩) then c0 else c1 := by
  have hw1 : S.width i = 1 := by simp [CSPSig.width, h]
  have hsingle : (Finset.univ : Finset (Fin (S.width i))) = {⟨0, hw⟩} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, fun x _ => ?_⟩
    apply Fin.ext; have := x.isLt; omega
  have hmax : S.maxVal i = c1 := by simp [CSPSig.maxVal, CSPSig.nth, h, hw1]
  have hgap : S.gap i ⟨0, hw⟩ = c1 - c0 := by simp [CSPSig.gap, CSPSig.nth, h]
  unfold Valuation.intValue
  rw [hsingle, Finset.sum_singleton, hmax, hgap]
  by_cases hb : v (.thr i ⟨0, hw⟩) = true
  · rw [if_pos hb, if_pos hb]; ring
  · rw [if_neg hb, if_neg hb]; ring

/-- The bottom-threshold literals of a list of width-≥1 integer variables. -/
def notAllEqualLits (vars : List (Fin S.nInt)) (hw : ∀ i ∈ vars, 0 < S.width i) :
    List (Lit (PBVar S)) :=
  vars.attach.map (fun x => Lit.pos (PBVar.thr x.1 ⟨0, hw x.1 x.2⟩))

/-- Encode "the integer variables `vars` are not all equal" via their bottom
    threshold bits (sound for a shared **binary** domain — see
    `encodeNotAllEqualBin_sound`). -/
def encodeNotAllEqualBin (vars : List (Fin S.nInt)) (hw : ∀ i ∈ vars, 0 < S.width i) :
    List (SignedPBConstr (PBVar S)) :=
  encodeNotAllEqual (notAllEqualLits vars hw)

/-- **Soundness (binary domain).** If the variables share the two-element domain
    `[c0, c1]` and two of their recovered values differ (the tuple is not all
    equal), then every encoded clause holds. -/
theorem encodeNotAllEqualBin_sound (v : Valuation S) (vars : List (Fin S.nInt))
    (c0 c1 : Int) (hw : ∀ i ∈ vars, 0 < S.width i)
    (hdom : ∀ i ∈ vars, S.values i = [c0, c1])
    (hne : ∃ i ∈ vars, ∃ i' ∈ vars, v.intValue i ≠ v.intValue i') :
    ∀ c ∈ encodeNotAllEqualBin vars hw, c.sat v := by
  obtain ⟨i, hi, i', hi', hii⟩ := hne
  have hvi := intValue_binary v i c0 c1 (hdom i hi) (hw i hi)
  have hvi' := intValue_binary v i' c0 c1 (hdom i' hi') (hw i' hi')
  have hmem_i : Lit.pos (PBVar.thr i ⟨0, hw i hi⟩) ∈ notAllEqualLits vars hw := by
    rw [notAllEqualLits, List.mem_map]; exact ⟨⟨i, hi⟩, List.mem_attach _ _, rfl⟩
  have hmem_i' : Lit.pos (PBVar.thr i' ⟨0, hw i' hi'⟩) ∈ notAllEqualLits vars hw := by
    rw [notAllEqualLits, List.mem_map]; exact ⟨⟨i', hi'⟩, List.mem_attach _ _, rfl⟩
  apply encodeNotAllEqual_sound v (notAllEqualLits vars hw)
  · -- some literal true
    by_cases hbi : v (.thr i ⟨0, hw i hi⟩) = true
    · exact ⟨_, hmem_i, by simp [evalLit, hbi]⟩
    · refine ⟨_, hmem_i', ?_⟩
      have hbi' : v (.thr i' ⟨0, hw i' hi'⟩) = true := by
        by_contra hc; exact hii (by rw [hvi, hvi', if_neg hbi, if_neg hc])
      simp [evalLit, hbi']
  · -- some literal false
    by_cases hbi : v (.thr i ⟨0, hw i hi⟩) = true
    · refine ⟨_, hmem_i', ?_⟩
      have hbi' : ¬ v (.thr i' ⟨0, hw i' hi'⟩) = true := by
        intro hc; exact hii (by rw [hvi, hvi', if_pos hbi, if_pos hc])
      simp [evalLit, hbi']
    · exact ⟨_, hmem_i, by simp [evalLit, hbi]⟩

end

end CSP.L2S.PB
