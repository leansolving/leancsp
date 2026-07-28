import CSP.L2S.Backends.PB.Bench.Generators
import CSP.L2S.Equivalence
import CSP.L2S.Proofs.PatternBridges
import Mathlib.Tactic

/-!
# Parametric symmetry breaking for Langford's problem `L(2,n)`

`gen_langford n` places `1,1,…,n,n` in `2n` positions so the two copies of digit `d` are `d+2`
apart, encoded with one position variable per `(digit, copy)`.  Its only non-trivial symmetry is
the **sequence reversal** `p ↦ 2n+1-p`, which on the variables is the *composite* of a value
reflection and the copy-swap (the reversed first copy is the old second copy).  It is therefore
neither a pure domain nor a pure variable symmetry, so we prove **equisatisfiability directly**:
`langRev` maps every solution to a solution, and the break `x₀ ≥ n` (the upper-half representative)
is satisfied by a solution or its reversal.  `langford_unsat_of_rev` bridges UNSAT of the extended
CSP to UNSAT of the base.  The equivalent lower-half break `x₀ ≤ n-1` (the mirror image, `langford_sbc'`)
is proved by the primed lemmas (`langford_sbc_break'`, `langford_equisat'`, `langford_unsat_of_rev'`).
Parametric in `n`.
-/

namespace CSP.L2S.PB.LangfordSB

open CSP.L2S IntCSP

/-! ### The copy-swap on variable indices -/

/-- Swap the two copies of a digit: even `2d ↔ 2d+1`. -/
def swapNat (j : ℕ) : ℕ := if j % 2 = 0 then j + 1 else j - 1

lemma swapNat_invol (j : ℕ) : swapNat (swapNat j) = j := by
  unfold swapNat
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · simp only [if_pos h, if_neg (show ¬ (j + 1) % 2 = 0 by omega)]; omega
  · simp only [if_neg (show ¬ j % 2 = 0 by omega), if_pos (show (j - 1) % 2 = 0 by omega)]; omega

lemma swapNat_lt {n j : ℕ} (hj : j < n * 2) : swapNat j < n * 2 := by
  unfold swapNat; split_ifs with h <;> omega

lemma swapNat_inj {j k : ℕ} (h : swapNat j = swapNat k) : j = k := by
  have := congrArg swapNat h; rwa [swapNat_invol, swapNat_invol] at this

/-! ### The reversal as an assignment transformation -/

/-- The sequence reversal acting on an assignment: reflect the value (`2n+1-·`) and swap copies. -/
def langRev (n : ℕ) (a : IntAssignment (n * 2)) : IntAssignment (n * 2) :=
  fun k => ((n * 2 + 1 : ℕ) : ℤ) - valAt a (swapNat k.val)

@[simp] lemma langRev_apply (n : ℕ) (a : IntAssignment (n * 2)) (k : Fin (n * 2)) :
    langRev n a k = ((n * 2 + 1 : ℕ) : ℤ) - valAt a (swapNat k.val) := rfl

/-- `valAt (langRev n a) v = (2n+1) - valAt a (swapNat v)` for in-range `v`. -/
lemma valAt_langRev {n : ℕ} (a : IntAssignment (n * 2)) (v : ℕ) (hv : v < n * 2) :
    valAt (langRev n a) v = ((n * 2 + 1 : ℕ) : ℤ) - valAt a (swapNat v) := by
  simp only [valAt, hv, dif_pos, langRev_apply]

/-! ### Facts extracted from a Langford solution -/

variable {n : ℕ} {a : IntAssignment (n * 2)}

/-- Every position variable holds a value in `[1, 2n]`. -/
lemma sol_bound (hsol : isSolutionInt (Bench.gen_langford n) a) (i : ℕ) (hi : i < n * 2) :
    1 ≤ valAt a i ∧ valAt a i ≤ ((n * 2 : ℕ) : ℤ) := by
  have hmem : IntConstraint.bound i 1 ((n * 2 : ℕ) : ℤ) ∈ (Bench.gen_langford n).constraints :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))
  have := hsol _ hmem
  simpa only [satisfiesConstraintInt, patternHolds, valAt] using this

/-- The two copies of digit `d0` are `d0+2` apart. -/
lemma sol_spacing (hsol : isSolutionInt (Bench.gen_langford n) a) (d0 : ℕ) (hd : d0 < n) :
    valAt a (d0 * 2 + 1) - valAt a (d0 * 2) = (d0 : ℤ) + 2 := by
  have h1 : d0 * 2 < n * 2 := by omega
  have h2 : d0 * 2 + 1 < n * 2 := by omega
  have hmem : (linear_eq (⟨#[⟨d0 * 2 + 1, h2⟩, ⟨d0 * 2, h1⟩], rfl⟩ : _root_.Vector (VarType (n * 2)) 2)
      (⟨#[1, -1], rfl⟩ : _root_.Vector ℤ 2) ((d0 : ℤ) + 2)) ∈ (Bench.gen_langford n).constraints := by
    refine List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr ?_)))
    refine List.mem_filterMap.mpr ⟨d0, List.mem_range.mpr hd, ?_⟩
    rw [dif_pos h1, dif_pos h2]
  have hkey := hsol _ hmem
  simp only [satisfiesConstraintInt, linear_eq, linear_rel, patternHolds,
    relHolds, _root_.Vector.toList, List.map_cons, List.map_nil, List.zipWith_cons_cons,
    List.zipWith_nil_right, List.sum_cons, List.sum_nil, one_mul, neg_one_mul, add_zero] at hkey
  rw [sub_eq_add_neg]; exact hkey

/-- A solution assigns distinct values, i.e. `a` is injective. -/
lemma sol_inj (hsol : isSolutionInt (Bench.gen_langford n) a) : Function.Injective a := by
  have hmem : alldifferent (_root_.Vector.ofFn id) ∈ (Bench.gen_langford n).constraints :=
    List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
  have hnd := (alldifferent_holds_iff _ a).mp (hsol _ hmem)
  have heq : (_root_.Vector.ofFn (id : Fin (n * 2) → Fin (n * 2))).toList.map a = List.ofFn a := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  exact List.nodup_ofFn.mp (heq ▸ hnd)

/-! ### The reversal maps solutions to solutions -/

theorem langRev_sol (hsol : isSolutionInt (Bench.gen_langford n) a) :
    isSolutionInt (Bench.gen_langford n) (langRev n a) := by
  intro c hc
  have hc2 : c ∈ ((List.range (n * 2)).map (fun i => IntConstraint.bound i 1 ((n * 2 : ℕ) : ℤ)))
      ++ ((List.range n).filterMap (fun d0 => if h1 : d0 * 2 < n * 2 then if h2 : d0 * 2 + 1 < n * 2
          then some (linear_eq (⟨#[⟨d0 * 2 + 1, h2⟩, ⟨d0 * 2, h1⟩], rfl⟩ : _root_.Vector (VarType (n * 2)) 2)
            (⟨#[1, -1], rfl⟩ : _root_.Vector ℤ 2) ((d0 : ℤ) + 2)) else none else none))
      ++ [alldifferent (_root_.Vector.ofFn id)] := hc
  rcases List.mem_append.mp hc2 with hbs | halld
  rcases List.mem_append.mp hbs with hb | hsp
  · -- bound
    obtain ⟨i, hir, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hir
    obtain ⟨hlo, hhi⟩ := sol_bound hsol (swapNat i) (swapNat_lt hir)
    simp only [satisfiesConstraintInt, patternHolds]
    show (1 : ℤ) ≤ valAt (langRev n a) i ∧ valAt (langRev n a) i ≤ ((n * 2 : ℕ) : ℤ)
    rw [show valAt (langRev n a) i = ((n * 2 + 1 : ℕ) : ℤ) - valAt a (swapNat i)
          from valAt_langRev a i hir]
    push_cast at hlo hhi ⊢
    constructor <;> linarith
  · -- spacing
    obtain ⟨d0, hdr, hfm⟩ := List.mem_filterMap.mp hsp
    rw [List.mem_range] at hdr
    have h1 : d0 * 2 < n * 2 := by omega
    have h2 : d0 * 2 + 1 < n * 2 := by omega
    rw [dif_pos h1, dif_pos h2] at hfm
    rw [← Option.some.inj hfm]
    have hsp0 := sol_spacing hsol d0 hdr
    simp only [satisfiesConstraintInt, linear_eq, linear_rel, patternHolds, relHolds,
      _root_.Vector.toList, List.map_cons, List.map_nil, List.zipWith_cons_cons,
      List.zipWith_nil_right, List.sum_cons, List.sum_nil, one_mul, neg_one_mul, add_zero]
    show valAt (langRev n a) (d0 * 2 + 1) + -valAt (langRev n a) (d0 * 2) = ((d0 : ℤ) + 2)
    rw [show valAt (langRev n a) (d0 * 2 + 1) = ((n * 2 + 1 : ℕ) : ℤ) - valAt a (swapNat (d0 * 2 + 1))
          from valAt_langRev a (d0 * 2 + 1) h2,
        show valAt (langRev n a) (d0 * 2) = ((n * 2 + 1 : ℕ) : ℤ) - valAt a (swapNat (d0 * 2))
          from valAt_langRev a (d0 * 2) h1,
        show swapNat (d0 * 2 + 1) = d0 * 2 by unfold swapNat; split_ifs <;> omega,
        show swapNat (d0 * 2) = d0 * 2 + 1 by unfold swapNat; split_ifs <;> omega]
    linarith [hsp0]
  · -- alldifferent
    obtain rfl := List.eq_of_mem_singleton halld
    apply (alldifferent_holds_iff (_root_.Vector.ofFn (id : Fin (n * 2) → Fin (n * 2)))
      (langRev n a)).mpr
    have hinj : Function.Injective (langRev n a) := by
      intro x y hxy
      simp only [langRev_apply] at hxy
      have hv : valAt a (swapNat x.val) = valAt a (swapNat y.val) := by linarith
      rw [valAt, valAt, dif_pos (swapNat_lt x.isLt), dif_pos (swapNat_lt y.isLt)] at hv
      exact Fin.ext (swapNat_inj (congrArg Fin.val (sol_inj hsol hv)))
    have heq : (_root_.Vector.ofFn (id : Fin (n * 2) → Fin (n * 2))).toList.map (langRev n a)
        = List.ofFn (langRev n a) := by
      apply List.ext_getElem (by simp); intro i h1 h2; simp
    exact heq ▸ List.nodup_ofFn.mpr hinj

/-! ### The upper-half break `x₀ ≥ n` is satisfied by a solution or its reversal -/

theorem langford_sbc_break (hn : 1 ≤ n) (hsol : isSolutionInt (Bench.gen_langford n) a) :
    satisfiesConstraintInt (Bench.langford_sbc n) a ∨
    satisfiesConstraintInt (Bench.langford_sbc n) (langRev n a) := by
  simp only [Bench.langford_sbc, satisfiesConstraintInt, patternHolds]
  by_cases h : valAt a 0 ≥ (n : ℤ)
  · exact Or.inl h
  · refine Or.inr ?_
    have hsp0 := sol_spacing hsol 0 hn
    rw [valAt_langRev a 0 (by omega), show swapNat 0 = 1 by unfold swapNat; rfl]
    simp only [Nat.zero_mul, Nat.zero_add] at hsp0
    push_cast at h ⊢
    omega

theorem langford_equisat (hn : 1 ≤ n) :
    equisatisfiable (Bench.gen_langford n)
      ((Bench.gen_langford n).addConstraint (Bench.langford_sbc n)) := by
  constructor
  · rintro ⟨a, hsol⟩
    rcases langford_sbc_break hn hsol with hsb | hsb
    · exact ⟨a, fun c hc => by rcases List.mem_cons.mp hc with rfl | hm; exacts [hsb, hsol c hm]⟩
    · exact ⟨langRev n a, fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hm; exacts [hsb, langRev_sol hsol c hm]⟩
  · rintro ⟨a, hsol⟩
    exact ⟨a, fun c hc => hsol c (List.mem_cons.mpr (Or.inr hc))⟩

theorem langford_unsat_of_rev (hn : 1 ≤ n)
    (h_unsat : ¬ isSatisfiableInt ((Bench.gen_langford n).addConstraint (Bench.langford_sbc n))) :
    ¬ isSatisfiableInt (Bench.gen_langford n) :=
  fun hb => h_unsat ((langford_equisat hn).mp hb)

/-! ### Lower-half break `x₀ ≤ n-1` (`langford_sbc'`) — the mirror image, equally sound -/

theorem langford_sbc_break' (hn : 1 ≤ n) (hsol : isSolutionInt (Bench.gen_langford n) a) :
    satisfiesConstraintInt (Bench.langford_sbc' n) a ∨
    satisfiesConstraintInt (Bench.langford_sbc' n) (langRev n a) := by
  simp only [Bench.langford_sbc', satisfiesConstraintInt, patternHolds]
  by_cases h : valAt a 0 ≤ (n : ℤ) - 1
  · exact Or.inl h
  · refine Or.inr ?_
    have hsp0 := sol_spacing hsol 0 hn
    rw [valAt_langRev a 0 (by omega), show swapNat 0 = 1 by unfold swapNat; rfl]
    simp only [Nat.zero_mul, Nat.zero_add] at hsp0
    push_cast at h ⊢
    omega

theorem langford_equisat' (hn : 1 ≤ n) :
    equisatisfiable (Bench.gen_langford n)
      ((Bench.gen_langford n).addConstraint (Bench.langford_sbc' n)) := by
  constructor
  · rintro ⟨a, hsol⟩
    rcases langford_sbc_break' hn hsol with hsb | hsb
    · exact ⟨a, fun c hc => by rcases List.mem_cons.mp hc with rfl | hm; exacts [hsb, hsol c hm]⟩
    · exact ⟨langRev n a, fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hm; exacts [hsb, langRev_sol hsol c hm]⟩
  · rintro ⟨a, hsol⟩
    exact ⟨a, fun c hc => hsol c (List.mem_cons.mpr (Or.inr hc))⟩

theorem langford_unsat_of_rev' (hn : 1 ≤ n)
    (h_unsat : ¬ isSatisfiableInt ((Bench.gen_langford n).addConstraint (Bench.langford_sbc' n))) :
    ¬ isSatisfiableInt (Bench.gen_langford n) :=
  fun hb => h_unsat ((langford_equisat' hn).mp hb)

end CSP.L2S.PB.LangfordSB
