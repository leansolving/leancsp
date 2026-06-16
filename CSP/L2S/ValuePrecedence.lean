import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import Mathlib.Order.PiLex
import Mathlib.Tactic

/-!
# Value precedence as a domain symmetry-breaking constraint

The `value_precedence colors` constraint (Law–Lee 2004) is proven to be a
`domainSymmetryBreakingConstraint` for any CSP whose solution set is closed under all
colour permutations preserving the colour interval `[0, colors-1]`.  It therefore plugs into
the project's symmetry-breaking machinery: `domainSymmetryBreaking_equisatisfiability` gives
equisatisfiability and `unsat_of_domain_sbc` (in `CSP/L2S/Symmetry.lean`) gives the end-to-end
`¬ csp.isSatisfiableInt` from a PB UNSAT certificate of the extended CSP.

## Construction of the symmetry `δ` (what the framework requires)

`domainSymmetryBreakingConstraint` asks, for each solution `a`, for a *single* domain symmetry
`δ` such that `δ ∘ a` solves the extended CSP.  We take `δ` to be the **lexicographically
minimal element of `a`'s colour-orbit** `{ δ' ∘ a | δ' interval-preserving }` (a finite set).
Its minimality forces `δ ∘ a` to respect value precedence: otherwise, at the least violating
position `p` (colour `v := (δ∘a) p ≥ 1` with no `v-1` earlier), composing with the colour
transposition `swap(v-1, v)` stays in the orbit and is strictly lex-smaller — a contradiction.
-/

namespace CSP.L2S

open IntCSP
open scoped Classical

-- ============================================================================
-- Interval-preserving permutation helpers
-- ============================================================================

/-- The identity preserves every interval. -/
lemma intervalPreserving_refl (lb ub : ℤ) : intervalPreserving (Equiv.refl ℤ) lb ub := by
  intro d; simp only [Equiv.refl_apply]

/-- A composition of interval-preserving permutations is interval-preserving. -/
lemma intervalPreserving_comp {δ e : Equiv.Perm ℤ} {lb ub : ℤ}
    (hδ : intervalPreserving δ lb ub) (he : intervalPreserving e lb ub) :
    intervalPreserving (δ.trans e) lb ub := by
  intro d; rw [Equiv.trans_apply]; exact (hδ d).trans (he (δ d))

/-- Swapping two values inside `[lb, ub]` preserves the interval. -/
lemma intervalPreserving_swap (c1 c2 lb ub : ℤ)
    (h1 : lb ≤ c1 ∧ c1 ≤ ub) (h2 : lb ≤ c2 ∧ c2 ≤ ub) :
    intervalPreserving (Equiv.swap c1 c2) lb ub := by
  intro d
  constructor
  · intro hd
    by_cases e1 : d = c1
    · rw [e1, Equiv.swap_apply_left]; exact h2
    · by_cases e2 : d = c2
      · rw [e2, Equiv.swap_apply_right]; exact h1
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2]; exact hd
  · intro hd
    by_cases e1 : d = c1
    · rw [e1]; exact h1
    · by_cases e2 : d = c2
      · rw [e2]; exact h2
      · rw [Equiv.swap_apply_of_ne_of_ne e1 e2] at hd; exact hd

-- ============================================================================
-- Lex-minimality core
-- ============================================================================

/-- If `b ≤ₗₑₓ b'`, they agree strictly before `p`, then `b p ≤ b' p` — so a strictly-smaller
    value at `p` is impossible. -/
private theorem lex_swap_contra {n : ℕ} (b b' : Fin n → ℤ) (p : Fin n)
    (hle : toLex b ≤ toLex b') (hagree : ∀ q : Fin n, q.val < p.val → b q = b' q)
    (hp : b' p < b p) : False := by
  have hkey : b p ≤ b' p := Pi.apply_le_of_toLex hle (fun j hj => hagree j (Fin.lt_def.mp hj))
  omega

-- ============================================================================
-- Value precedence is a domain symmetry-breaking constraint
-- ============================================================================

/-- **Value precedence is a domain symmetry-breaking constraint.**  If every solution of `csp`
    colours in `[0, colors-1]` and every interval-preserving colour permutation is a domain
    symmetry, then `value_precedence colors` is a domain symmetry-breaking constraint. -/
theorem value_precedence_is_domain_symmetry_breaking {colors : ℕ} (csp : IntCSP)
    (hdom : ∀ b : IntAssignment csp.num_vars, isSolutionInt csp b →
      ∀ j : Fin csp.num_vars, 0 ≤ b j ∧ b j ≤ (colors : ℤ) - 1)
    (hsym : ∀ δ : Equiv.Perm ℤ, intervalPreserving δ 0 ((colors : ℤ) - 1) → DomainSymmetry csp δ) :
    domainSymmetryBreakingConstraint csp (value_precedence colors) := by
  intro a ha
  have ha_dom : ∀ j, 0 ≤ a j ∧ a j ≤ (colors : ℤ) - 1 := hdom a ha
  -- The colour-orbit of `a` (a finite set), and its lex-minimal element.
  set Orbit : Set (IntAssignment csp.num_vars) :=
    {b | ∃ δ : Equiv.Perm ℤ, intervalPreserving δ 0 ((colors : ℤ) - 1) ∧ b = ⇑δ ∘ a} with hOrbit
  have hfin : Orbit.Finite := by
    apply Set.Finite.subset
      (Set.Finite.pi (fun _ : Fin csp.num_vars => Set.finite_Ico (0 : ℤ) (colors : ℤ)))
    rintro b ⟨δ, hδ, rfl⟩
    refine Set.mem_pi.mpr (fun j _ => Set.mem_Ico.mpr ?_)
    have := (hδ (a j)).mp (ha_dom j)
    simp only [Function.comp_apply]; omega
  have hne : Orbit.Nonempty :=
    ⟨a, Equiv.refl ℤ, intervalPreserving_refl 0 _, by simp only [Equiv.coe_refl, Function.id_comp]⟩
  obtain ⟨b, hbOrbit, hbmin⟩ := Set.exists_min_image Orbit toLex hfin hne
  obtain ⟨δ, hδip, hbeq⟩ := hbOrbit
  have hbdom : ∀ j, 0 ≤ b j ∧ b j ≤ (colors : ℤ) - 1 := by
    intro j; rw [hbeq]; simp only [Function.comp_apply]; exact (hδip (a j)).mp (ha_dom j)
  -- `b = δ ∘ a` respects value precedence.
  have hVP : ∀ j : Fin csp.num_vars, 1 ≤ b j → ∃ i : Fin csp.num_vars, i.val < j.val ∧ b i = b j - 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j0, hj0pos, hj0⟩ := hcon
    have hviol_ne : (Finset.univ.filter
        (fun j : Fin csp.num_vars => 1 ≤ b j ∧ ∀ i : Fin csp.num_vars, i.val < j.val → b i ≠ b j - 1)).Nonempty :=
      ⟨j0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj0pos, hj0⟩⟩
    obtain ⟨p, hpmem, hpmin⟩ := Finset.exists_min_image _ (fun j : Fin csp.num_vars => j.val) hviol_ne
    rw [Finset.mem_filter] at hpmem
    obtain ⟨_, hppos, hpno⟩ := hpmem
    -- `swap(v-1, v) ∘ b` is in the orbit (compose the interval-preserving perms).
    have hbp := hbdom p
    have hswap_ip : intervalPreserving (Equiv.swap (b p - 1) (b p)) 0 ((colors : ℤ) - 1) :=
      intervalPreserving_swap (b p - 1) (b p) 0 ((colors : ℤ) - 1)
        ⟨Int.sub_nonneg_of_le hppos, (sub_one_lt (b p)).le.trans hbp.2⟩ ⟨hbp.1, hbp.2⟩
    have hb'Orbit : (⇑(Equiv.swap (b p - 1) (b p)) ∘ b) ∈ Orbit := by
      refine ⟨δ.trans (Equiv.swap (b p - 1) (b p)), intervalPreserving_comp hδip hswap_ip, ?_⟩
      rw [hbeq]; funext x; simp only [Function.comp_apply, Equiv.trans_apply]
    have hle : toLex b ≤ toLex (⇑(Equiv.swap (b p - 1) (b p)) ∘ b) := hbmin _ hb'Orbit
    -- They agree strictly before `p` (neither `v` nor `v-1` occurs there).
    have hagree : ∀ q : Fin csp.num_vars, q.val < p.val →
        b q = (⇑(Equiv.swap (b p - 1) (b p)) ∘ b) q := by
      intro q hq
      have hne1 : b q ≠ b p - 1 := hpno q hq
      have hne2 : b q ≠ b p := by
        intro hcontra
        by_cases hqviol : ∀ i : Fin csp.num_vars, i.val < q.val → b i ≠ b q - 1
        · have : p.val ≤ q.val := hpmin q (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨by rw [hcontra]; exact hppos, hqviol⟩)
          omega
        · push Not at hqviol
          obtain ⟨i, hiq, hival⟩ := hqviol
          exact hpno i (by omega) (by rw [hcontra] at hival; exact hival)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    have hbp' : (⇑(Equiv.swap (b p - 1) (b p)) ∘ b) p < b p := by
      have hval : (⇑(Equiv.swap (b p - 1) (b p)) ∘ b) p = b p - 1 := by
        simp only [Function.comp_apply, Equiv.swap_apply_right]
      rw [hval]; exact sub_one_lt (b p)
    exact lex_swap_contra b (⇑(Equiv.swap (b p - 1) (b p)) ∘ b) p hle hagree hbp'
  -- Assemble the symmetry-breaking witness `δ`.
  refine ⟨δ, hsym δ hδip, ?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with hvp | horig
  · subst hvp
    show patternHolds (value_precedence colors) (⇑δ ∘ a)
    rw [← hbeq]; exact hVP
  · exact hsym δ hδip a ha c horig

end CSP.L2S
