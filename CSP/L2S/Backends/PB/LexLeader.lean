import CSP.L2S.Backends.PB.LinearNe
import CSP.L2S.Backends.PB.Compose
import Mathlib.Data.Fin.Rev

/-!
# PB encoding of the strict lexicographic reversal leader `x <_lex rev(x)`

Over a `{0,1,2}` domain the leader is encoded as the single Big-M linear
disequality `Σᵢ (3ⁱ − 3^{rev i})·xᵢ ≠ 0`.  That form is `L(x) − L(rev x)` for the
base-3 value `L(x) = Σᵢ 3ⁱ·xᵢ`, which is injective on `{0,1,2}`-vectors, so the
form vanishes **iff** `x` is a palindrome.  Hence it is a sound relaxation of the
strict leader, and it is violated by every palindrome.

The encoder reuses `encodeLinearNe`; the new fact is `base3_nonvanish`.
-/

namespace CSP.L2S.PB

open CSPSig

/-! ### Base-3 non-vanishing (the mathematical core) -/

/-- **Balanced base-3 injectivity.**  A signed base-3 combination of digits in `[-2,2]`
    vanishes only when every digit is `0` (each digit is `≡` the sum mod 3, and `|d|≤2<3`
    forces it to `0`; then divide by `3` and recurse). -/
theorem base3_nonvanish (n : ℕ) (d : Fin n → ℤ) (hb : ∀ i, -2 ≤ d i ∧ d i ≤ 2)
    (hsum : ∑ i : Fin n, (3 : ℤ) ^ (i : ℕ) * d i = 0) : ∀ i, d i = 0 := by
  induction n with
  | zero => intro i; exact absurd i.isLt (by omega)
  | succ m ih =>
    rw [Fin.sum_univ_succ] at hsum
    have hfactor : (∑ j : Fin m, (3 : ℤ) ^ ((j.succ : Fin (m + 1)) : ℕ) * d j.succ)
        = 3 * ∑ j : Fin m, (3 : ℤ) ^ (j : ℕ) * d j.succ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hval : ((j.succ : Fin (m + 1)) : ℕ) = (j : ℕ) + 1 := by simp [Fin.val_succ]
      rw [hval, pow_succ]; ring
    rw [hfactor] at hsum
    simp only [Fin.val_zero, pow_zero, one_mul] at hsum
    have hd0 : d 0 = 0 := by have := hb 0; omega
    have hrest : (∑ j : Fin m, (3 : ℤ) ^ (j : ℕ) * d j.succ) = 0 := by omega
    have hih := ih (fun j => d j.succ) (fun j => hb j.succ) hrest
    intro i
    refine Fin.cases hd0 (fun j => hih j) i

/-! ### The coefficient list and its non-vanishing -/

variable {S : CSPSig}

/-- The signed base-3 mirror coefficients: variable `i` gets `3ⁱ − 3^{rev i}`. -/
def lexRevCoeffs (S : CSPSig) : List (Int × Fin S.nInt) :=
  (List.finRange S.nInt).map (fun i => ((3 : ℤ) ^ i.val - 3 ^ (Fin.rev i).val, i))

/-- **Soundness of the relaxation.**  On a `{0,1,2}` assignment that is not a palindrome,
    the base-3 mirror form is nonzero. -/
theorem lexRevCoeffs_sum_ne (a : Fin S.nInt → Int)
    (hb : ∀ i, 0 ≤ a i ∧ a i ≤ 2) (hne : ∃ i, a i ≠ a (Fin.rev i)) :
    ((lexRevCoeffs S).map (fun p => p.1 * a p.2)).sum ≠ 0 := by
  have hlist : ((lexRevCoeffs S).map (fun p => p.1 * a p.2)).sum
      = ∑ i : Fin S.nInt, ((3 : ℤ) ^ (i : ℕ) - 3 ^ (Fin.rev i : ℕ)) * a i := by
    simp only [lexRevCoeffs, List.map_map]
    simp [List.sum_ofFn, ← List.ofFn_eq_map]
  rw [hlist]
  -- rewrite as the base-3 sum of the mirror-difference digits
  have hreindex : ∑ i : Fin S.nInt, (3 : ℤ) ^ (Fin.rev i : ℕ) * a i
      = ∑ i : Fin S.nInt, (3 : ℤ) ^ (i : ℕ) * a (Fin.rev i) := by
    symm; apply Fintype.sum_equiv (Fin.revPerm); intro i; simp [Fin.rev_rev]
  have hrw : ∑ i : Fin S.nInt, ((3 : ℤ) ^ (i : ℕ) - 3 ^ (Fin.rev i : ℕ)) * a i
      = ∑ i : Fin S.nInt, (3 : ℤ) ^ (i : ℕ) * (a i - a (Fin.rev i)) := by
    rw [show (∑ i : Fin S.nInt, ((3 : ℤ) ^ (i : ℕ) - 3 ^ (Fin.rev i : ℕ)) * a i)
          = ∑ i : Fin S.nInt, ((3 : ℤ) ^ (i : ℕ) * a i - (3 : ℤ) ^ (Fin.rev i : ℕ) * a i)
        from Finset.sum_congr rfl (fun i _ => by ring),
        show (∑ i : Fin S.nInt, (3 : ℤ) ^ (i : ℕ) * (a i - a (Fin.rev i)))
          = ∑ i : Fin S.nInt, ((3 : ℤ) ^ (i : ℕ) * a i - (3 : ℤ) ^ (i : ℕ) * a (Fin.rev i))
        from Finset.sum_congr rfl (fun i _ => by ring),
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, hreindex]
  rw [hrw]
  intro hzero
  obtain ⟨i0, hi0⟩ := hne
  have hbd : ∀ i, -2 ≤ a i - a (Fin.rev i) ∧ a i - a (Fin.rev i) ≤ 2 := by
    intro i; have h1 := hb i; have h2 := hb (Fin.rev i); omega
  have := base3_nonvanish S.nInt (fun i => a i - a (Fin.rev i)) hbd hzero i0
  omega

/-! ### The soundness-carrying encoded constraint -/

/-- The leader `x <_lex rev(x)` as an `EncConstr` over a signature whose every
    variable has domain `{0,1,2}`.  Reuses the Big-M linear-`≠` encoder on the
    base-3 mirror form; its precondition is "`x` is not a palindrome". -/
def encStrictLexRev (S : CSPSig) (base : ℕ) (hb : base < S.nAux)
    (hg : ∀ i : Fin S.nInt, S.values i = [0, 1, 2]) : EncConstr S where
  constrs := (encodeLinearNe (lexRevCoeffs S) 0 ⟨base, hb⟩).filterMap normalize
  pre := fun a => ∃ i : Fin S.nInt, a i ≠ a (Fin.rev i)
  setsAux := fun a =>
    [(⟨base, hb⟩, decide (((lexRevCoeffs S).map (fun p => p.1 * a p.2)).sum > 0))]
  sound := by
    intro a bA auxA hdom hpre hframe c hc
    have hdom012 : ∀ i, 0 ≤ a i ∧ a i ≤ 2 := by
      intro i
      have hmem := hdom i
      rw [hg i] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h <;> omega
    have hne : ((lexRevCoeffs S).map (fun p => p.1 * a p.2)).sum ≠ 0 :=
      lexRevCoeffs_sum_ne a hdom012 hpre
    have hauxs : auxA ⟨base, hb⟩
        = decide (((lexRevCoeffs S).map (fun p => p.1 * a p.2)).sum > 0) :=
      hframe (⟨base, hb⟩, decide (((lexRevCoeffs S).map (fun p => p.1 * a p.2)).sum > 0))
        (by simp)
    exact extend_sat_encodeLinearNe a bA auxA hdom (lexRevCoeffs S) 0 ⟨base, hb⟩
      (by simpa using hne) (by simpa using hauxs) c hc

end CSP.L2S.PB
