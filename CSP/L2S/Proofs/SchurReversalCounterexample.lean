import CSP.L2S.Proofs.SchurSB
import CSP.L2S.Proofs.SchurEquivalence
import CSP.L2S.Witness
import CSP.L2S.Backends.PB.Problems.SchurLexLeader
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.IntervalCases

/-!
# A cautionary example: an unsound reversal reformulation of Schur

The reversal-based strict lexicographic leader `x <_lex rev(x)` is a *sound*
symmetry break for van der Waerden and modular Schur, but **unsound** when
transplanted onto ordinary Schur.  Two independent facts, both proved at the
reformulation level with concrete witnesses and kernel `decide` — no UNSAT
pipeline, no `¬ isSatisfiableInt`:

1. **The reversal is not a variable symmetry of the Schur CSP** for every
   satisfiable size `3 ≤ n ≤ 12` (`reversal_not_schur_symmetry_range`).  E.g.
   `[0,1,1]` reverses to `[1,1,0]`, which colours `1 + 1 = 2` monochromatically.

2. **The strict reversal leader is not a valid symmetry break** at `n = 13`
   (`schur_strict_reversal_leader_unsound`).  There every solution is a palindrome,
   so the reversal fixes it; but a palindrome satisfies neither `s <_lex rev s` nor
   `rev s <_lex s`, so the strict leader deletes the whole orbit.  This is the
   deliberate negation of Langford's sound break `langford_sbc_break`.

We deliberately do *not* target the framework predicate
`¬ variableSymmetryBreakingConstraint` here: it quantifies over *all* variable
symmetries and would need "every `n = 13` solution is a palindrome", which in this
framework requires the PB certificate pipeline (see the end of the file).
-/

open CSP.L2S

namespace Schur

/-! ### Obligation 1: the reversal is not a variable symmetry (3 ≤ n ≤ 12) -/

/-- Per-size witness solutions of the 3-colour Schur CSP whose reversal is *not* a
    solution (found by brute force).  Each reversal makes some triple monochromatic.
    Sizes outside `3..12` are unused and map to the zero assignment. -/
def schurRevWitness : (n : ℕ) → IntAssignment n
  | 3  => ![0, 1, 1]
  | 4  => ![0, 1, 0, 2]
  | 5  => ![0, 1, 0, 2, 2]
  | 6  => ![0, 1, 0, 2, 0, 1]
  | 7  => ![0, 1, 0, 2, 0, 1, 1]
  | 8  => ![0, 1, 0, 2, 0, 2, 0, 1]
  | 9  => ![0, 1, 0, 2, 0, 2, 0, 1, 1]
  | 10 => ![0, 1, 0, 2, 1, 1, 2, 0, 2, 0]
  | 11 => ![0, 1, 0, 2, 1, 2, 2, 0, 2, 0, 1]
  | 12 => ![0, 1, 0, 2, 1, 2, 2, 0, 2, 0, 1, 0]
  | _  => fun _ => 0

/-- **The reversal is not a variable symmetry of the 3-colour Schur CSP for `3 ≤ n ≤ 12`.**
    Each size is a separate concrete instance discharged by its witness and `decide`.
    The range is tight: at `n = 1, 2` the reversal is accidentally a symmetry, at
    `n = 13` all solutions are palindromes, and at `n ≥ 14` the CSP is UNSAT. -/
theorem reversal_not_schur_symmetry_range
    (n : ℕ) (h3 : 3 ≤ n) (h12 : n ≤ 12) :
    ¬ VariableSymmetry (schur_csp_triples n 3 (schurTriples n)) Fin.revPerm := by
  intro hsym
  interval_cases n <;>
    exact absurd (hsym (schurRevWitness _) (by decide)) (by decide)

/-- **The reversal is not a variable symmetry of `schur 3 3`.** Witness `[0,1,1]` is a
    solution whose reversal `[1,1,0]` is monochromatic on the triple `1 + 1 = 2`. -/
theorem reversal_not_schur_symmetry :
    ¬ VariableSymmetry (schur_csp_triples 3 3 (schurTriples 3)) Fin.revPerm :=
  reversal_not_schur_symmetry_range 3 (by decide) (by decide)

/-! ### Obligation 2: the strict reversal leader is not a valid symmetry break (n = 13) -/

/-- The strict lexicographic reversal leader `x <_lex rev(x)`, as a standalone decidable
    predicate on assignments: some position `p` is the first at which `x` and its reversal
    differ, and there `x` is strictly smaller. A palindrome (`x = rev x`) never satisfies
    it.  Kept out of the `IntConstraint` inductive on purpose: fact 2 is refuted at
    the reformulation level, so the leader need only be a predicate. -/
def strictLexRevLt {n : ℕ} (a : IntAssignment n) : Prop :=
  ∃ p : Fin n, (∀ q : Fin n, q < p → a q = a (Fin.rev q)) ∧ a p < a (Fin.rev p)

instance instDecStrictLexRevLt {n : ℕ} (a : IntAssignment n) :
    Decidable (strictLexRevLt a) := by
  unfold strictLexRevLt; infer_instance

/-- **The strict reversal leader is not a valid symmetry break for Schur at `n = 13`.**
    The committed palindrome solution `s = [0,1,1,0,2,2,0,2,2,0,1,1,0]`
    (= `CSP/L2S/EndToEnd/sols/schur_c3_n13.sol`) is fixed by the reversal (`rev s = s`),
    and satisfies neither `s <_lex rev s` nor `rev s <_lex rev(rev s)`. So the reversal
    symmetry maps its whole orbit `{s, rev s} = {s}` off the strict leader: no member
    survives, and the augmented model would be wrongly UNSAT — the false-certificate
    mechanism, shown here without the UNSAT pipeline.

    Contrast: the *non-strict* leader retains `s` — see
    `schur_nonstrict_reversal_leader_retains`. And the analogous *sound* break for a
    reversal symmetry is `CSP.L2S.PB.LangfordSB.langford_sbc_break`. -/
theorem schur_strict_reversal_leader_unsound :
    ∃ a : IntAssignment 13,
      IntCSP.isSolutionInt (schur_csp_triples 13 3 (schurTriples 13)) a ∧
      ¬ (strictLexRevLt a ∨ strictLexRevLt (a ∘ Fin.revPerm)) := by
  refine ⟨![0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0], ?_, ?_⟩
  · decide
  · decide

/-! ### Companion: the non-strict leader retains the palindrome (strictness is the culprit) -/

/-- The *non-strict* lexicographic reversal leader `x ≤_lex rev(x)`: strictly smaller at
    the first difference, or equal to its reversal (a palindrome). -/
def leLexRev {n : ℕ} (a : IntAssignment n) : Prop :=
  strictLexRevLt a ∨ ∀ q : Fin n, a q = a (Fin.rev q)

instance instDecLeLexRev {n : ℕ} (a : IntAssignment n) :
    Decidable (leLexRev a) := by
  unfold leLexRev; infer_instance

/-- **The non-strict leader keeps the palindrome that the strict leader deletes.** The
    same `n = 13` solution satisfies `s ≤_lex rev s` (via the palindrome disjunct), so a
    non-strict `≤_lex` reversal leader is retained — pinpointing *strictness* as the cause
    of the unsoundness, and mirroring Langford's sound non-strict leader. -/
theorem schur_nonstrict_reversal_leader_retains :
    ∃ a : IntAssignment 13,
      IntCSP.isSolutionInt (schur_csp_triples 13 3 (schurTriples 13)) a ∧ leLexRev a := by
  refine ⟨![0, 1, 1, 0, 2, 2, 0, 2, 2, 0, 1, 1, 0], ?_, ?_⟩
  · decide
  · decide

/-! ### Obligation 2, framework level: the leader is not a variableSymmetryBreakingConstraint -/

/-!
The reformulation-level results above refute the reversal-symmetry-specific break. The
framework's `variableSymmetryBreakingConstraint` predicate quantifies over *all* variable
symmetries, so refuting it needs the full "every `n = 13` solution is a palindrome" fact —
which we obtain, kernel-checked, from the verified PB pipeline: `base13` is SAT (an
`S(3) = 13` witness) while `aug13 = base13 ⊕ strictLexRevLeader` is PB-UNSAT
(`SchurLexLeader.aug13_unsat`). The two together break equisatisfiability, and the
SBC⇒equisatisfiability theorem finishes it.
-/

open CSP.L2S.PB.SchurLexLeader in
/-- `base13` is satisfiable — an `S(3) = 13` colouring, kernel-checked from the committed
    witness (no `native_decide`; the witness is untrusted, re-checked by `decide`). -/
theorem base13_sat : base13.isSatisfiableInt :=
  csp_sat_file base13 "CSP/L2S/EndToEnd/sols/schur_c3_n13.sol"

open CSP.L2S.PB.SchurLexLeader in
/-- Adding the strict reversal leader breaks equisatisfiability: `base13` is SAT but the
    augmented CSP is UNSAT. -/
theorem base_aug_not_equisatisfiable :
    ¬ equisatisfiable base13 (base13.addConstraint leader) :=
  fun e => aug13_unsat (e.mp base13_sat)

open CSP.L2S.PB.SchurLexLeader in
/-- **The strict reversal leader is not a valid variable symmetry-breaking constraint** for
    the 3-colour Schur CSP at `n = 13`.  Were it one, it would preserve satisfiability
    (`variableSymmetryBreaking_equisatisfiability`); but it turns the SAT base CSP into the
    UNSAT `aug13`.  The framework-level form of the cautionary example, with the false
    UNSAT certificate supplied by the verified PB backend. -/
theorem schur_leader_not_variableSBC :
    ¬ variableSymmetryBreakingConstraint base13 leader :=
  mt (variableSymmetryBreaking_equisatisfiability base13 leader)
    base_aug_not_equisatisfiable

end Schur
