import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import Mathlib.Order.PiLex
import Mathlib.Tactic

/-!
# Value precedence preserves satisfiability

The `value_precedence colors` constraint (Law–Lee 2004) is a *symmetry-breaking* constraint for
any CSP whose solution set is closed under permutations of the interchangeable colour values
`{0, …, colors-1}`.  We prove that adding it preserves satisfiability, hence equisatisfiability,
hence (with a PB UNSAT certificate for the extended CSP) UNSAT of the original.

## Proof idea (no orbit/permutation construction needed)

Take the **lexicographically minimal** solution `b` (it exists: solutions have values in a finite
interval, so there are finitely many).  Then `b` satisfies value precedence: otherwise, at the
*least* violating position `p` (colour `v := b p ≥ 1` with no `v-1` earlier), swapping colours
`v-1` and `v` yields another solution (closure) that agrees with `b` before `p` and is smaller at
`p` (`v-1 < v`) — strictly lex-smaller, contradicting minimality.  The swap touches no earlier
position because, by minimality of `p`, neither `v` nor `v-1` occurs before `p`.
-/

namespace CSP.L2S

open IntCSP
open scoped Classical

/-- The lex-minimality contradiction: if `b ≤ₗₑₓ b'`, they agree strictly before `p`, then
    `b p ≤ b' p` — so a strictly-smaller value at `p` is impossible. -/
private theorem lex_swap_contra {n : ℕ} (b b' : Fin n → ℤ) (p : Fin n)
    (hle : toLex b ≤ toLex b') (hagree : ∀ q : Fin n, q.val < p.val → b q = b' q)
    (hp : b' p < b p) : False := by
  have hkey : b p ≤ b' p := Pi.apply_le_of_toLex hle (fun j hj => hagree j (Fin.lt_def.mp hj))
  omega

/-- **Value precedence preserves satisfiability.**  If `csp`'s solutions all take colours in
    `[0, colors)` and the solution set is closed under transposing any two such colours, then a
    solution of `csp` extends to a solution of `csp` together with the `value_precedence colors`
    constraint. -/
theorem value_precedence_preserves_satisfiability {colors : ℕ} (csp : IntCSP)
    (hdom : ∀ b : IntAssignment csp.num_vars, isSolutionInt csp b →
      ∀ j : Fin csp.num_vars, 0 ≤ b j ∧ b j < (colors : ℤ))
    (hclosure : ∀ c1 c2 : ℤ, 0 ≤ c1 → c1 < (colors : ℤ) → 0 ≤ c2 → c2 < (colors : ℤ) →
      ∀ b : IntAssignment csp.num_vars, isSolutionInt csp b →
        isSolutionInt csp (Equiv.swap c1 c2 ∘ b))
    (hsat : isSatisfiableInt csp) :
    isSatisfiableInt (csp.addConstraint (value_precedence colors)) := by
  obtain ⟨a, ha⟩ := hsat
  -- The (finite) set of all solutions.
  set S : Set (IntAssignment csp.num_vars) := {b | isSolutionInt csp b} with hS
  have hfin : S.Finite := by
    apply Set.Finite.subset
      (Set.Finite.pi (fun _ : Fin csp.num_vars => Set.finite_Ico (0 : ℤ) (colors : ℤ)))
    intro b hb
    refine Set.mem_pi.mpr (fun j _ => ?_)
    exact Set.mem_Ico.mpr (hdom b hb j)
  have hne : S.Nonempty := ⟨a, ha⟩
  obtain ⟨b, hbS, hbmin⟩ := Set.exists_min_image S toLex hfin hne
  have hbsol : isSolutionInt csp b := hbS
  -- `b` satisfies value precedence.
  have hVP : ∀ j : Fin csp.num_vars, 1 ≤ b j → ∃ i : Fin csp.num_vars, i.val < j.val ∧ b i = b j - 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j0, hj0pos, hj0⟩ := hcon
    -- The nonempty finite set of violating positions; pick one of least index.
    have hviol_ne : (Finset.univ.filter
        (fun j : Fin csp.num_vars => 1 ≤ b j ∧ ∀ i : Fin csp.num_vars, i.val < j.val → b i ≠ b j - 1)).Nonempty :=
      ⟨j0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hj0pos, hj0⟩⟩
    obtain ⟨p, hpmem, hpmin⟩ := Finset.exists_min_image _ (fun j : Fin csp.num_vars => j.val) hviol_ne
    rw [Finset.mem_filter] at hpmem
    obtain ⟨_, hppos, hpno⟩ := hpmem
    -- The swapped solution `b' = swap(v-1, v) ∘ b`.
    obtain ⟨hpd1, hpd2⟩ := hdom b hbsol p
    have hb'S : isSolutionInt csp (Equiv.swap (b p - 1) (b p) ∘ b) :=
      hclosure (b p - 1) (b p) (Int.sub_nonneg_of_le hppos) ((sub_one_lt (b p)).trans hpd2)
        hpd1 hpd2 b hbsol
    -- They agree strictly before `p` (neither `v` nor `v-1` occurs there).
    have hagree : ∀ q : Fin csp.num_vars, q.val < p.val →
        b q = (Equiv.swap (b p - 1) (b p) ∘ b) q := by
      intro q hq
      have hne1 : b q ≠ b p - 1 := hpno q hq
      have hne2 : b q ≠ b p := by
        intro hcontra
        -- if `b q = b p = v` for `q < p`, then `q` violates too, contradicting minimality of `p`
        by_cases hqviol : ∀ i : Fin csp.num_vars, i.val < q.val → b i ≠ b q - 1
        · have : p.val ≤ q.val := hpmin q (by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨by rw [hcontra]; exact hppos, hqviol⟩)
          omega
        · push Not at hqviol
          obtain ⟨i, hiq, hival⟩ := hqviol
          exact hpno i (by omega) (by rw [hcontra] at hival; exact hival)
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    -- `b'` is lex ≥ `b` (minimality) but strictly smaller at `p`.
    have hle : toLex b ≤ toLex (Equiv.swap (b p - 1) (b p) ∘ b) := hbmin _ hb'S
    have hbp' : (Equiv.swap (b p - 1) (b p) ∘ b) p < b p := by
      simp only [Function.comp_apply, Equiv.swap_apply_right]; exact sub_one_lt (b p)
    exact lex_swap_contra b (Equiv.swap (b p - 1) (b p) ∘ b) p hle hagree hbp'
  -- Assemble: `b` solves the extended CSP.
  refine ⟨b, ?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with hvp | horig
  · subst hvp
    show patternHolds (value_precedence colors) b
    exact hVP
  · exact hbsol c horig

/-- Equisatisfiability form of `value_precedence_preserves_satisfiability`. -/
theorem value_precedence_equisatisfiable {colors : ℕ} (csp : IntCSP)
    (hdom : ∀ b : IntAssignment csp.num_vars, isSolutionInt csp b →
      ∀ j : Fin csp.num_vars, 0 ≤ b j ∧ b j < (colors : ℤ))
    (hclosure : ∀ c1 c2 : ℤ, 0 ≤ c1 → c1 < (colors : ℤ) → 0 ≤ c2 → c2 < (colors : ℤ) →
      ∀ b : IntAssignment csp.num_vars, isSolutionInt csp b →
        isSolutionInt csp (Equiv.swap c1 c2 ∘ b)) :
    equisatisfiable csp (csp.addConstraint (value_precedence colors)) := by
  constructor
  · intro hsat; exact value_precedence_preserves_satisfiability csp hdom hclosure hsat
  · rintro ⟨b, hb⟩
    exact ⟨b, fun c hc => hb c (List.mem_cons_of_mem _ hc)⟩

/-- **End-to-end bridge for value precedence.**  Under colour-closure, UNSAT of the
    value-precedence-extended CSP yields UNSAT of the original. -/
theorem unsat_of_value_precedence {colors : ℕ} (csp : IntCSP)
    (hdom : ∀ b : IntAssignment csp.num_vars, isSolutionInt csp b →
      ∀ j : Fin csp.num_vars, 0 ≤ b j ∧ b j < (colors : ℤ))
    (hclosure : ∀ c1 c2 : ℤ, 0 ≤ c1 → c1 < (colors : ℤ) → 0 ≤ c2 → c2 < (colors : ℤ) →
      ∀ b : IntAssignment csp.num_vars, isSolutionInt csp b →
        isSolutionInt csp (Equiv.swap c1 c2 ∘ b))
    (h_unsat : ¬ isSatisfiableInt (csp.addConstraint (value_precedence colors))) :
    ¬ isSatisfiableInt csp :=
  fun hs => h_unsat (value_precedence_preserves_satisfiability csp hdom hclosure hs)

end CSP.L2S
