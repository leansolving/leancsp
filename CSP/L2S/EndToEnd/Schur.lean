import CSP.L2S.Backends.PB.Problems.SchurSBC
import CSP.L2S.Backends.PB.Problems.SchurVP
import CSP.L2S.Proofs.SchurValuePrecedence

/-!
# End-to-end UNSAT via symmetry breaking — Schur `S(2) < 5`

This module ties the two halves of the project together for the Schur problem:

1. **SBC correctness** (`Proofs/SchurSB.lean`): the colour-fixing constraint `x₀ = 0`
   is a *domain symmetry-breaking constraint* for the Schur CSP — proved from the fact
   that swapping two colours is a domain symmetry (`schur_colour_swap`), so it preserves
   equisatisfiability.
2. **Verified PB UNSAT** (`Problems/SchurSBC.lean`): the *extended* CSP
   `(schur_csp 5 2).addConstraint (x₀ = 0)` is UNSAT, certified by a kernel-checked
   pseudo-Boolean proof (`certs/schur_2_5_sbc.pbp`).

The bridge `CSP.L2S.unsat_of_sbc` (in `CSP/L2S/Symmetry.lean`) composes them: a verified
SBC plus UNSAT of the extended CSP yields UNSAT of the **original** CSP.

This is the template followed by every other family under `CSP/L2S/EndToEnd/`.
-/

namespace CSP.L2S.EndToEnd.Schur

open CSP.L2S CSP.L2S.PB

/-- **End-to-end `S(2) < 5`.** The original Schur CSP `{1,…,5}` 2-coloured with no
    monochromatic `x + y = z` is unsatisfiable — obtained from UNSAT of the
    *symmetry-broken* extended CSP (a kernel-checked PB certificate) via the verified
    colour-fixing symmetry-breaking constraint. The colours `S(2) = 4`, so five integers
    cannot be 2-coloured sum-free. -/
theorem schur_2_5_unsat : ¬ (_root_.Schur.schur_csp 5 2).isSatisfiableInt :=
  unsat_of_sbc _ _
    (_root_.Schur.schur_sbc_is_symmetry_breaking 5 2 (by decide) (by decide)
      (_root_.Schur.schurTriples 5))
    PB.SchurSBC.sb_schur_2_5_unsat

/-- **End-to-end `S(3) < 14`.** The original Schur CSP `{1,…,14}` 3-coloured with no
    monochromatic `x + y = z` is unsatisfiable (`S(3) = 13`), recovered from the
    symmetry-broken extended CSP via the verified colour-fixing SBC. -/
theorem schur_3_14_unsat : ¬ (_root_.Schur.schur_csp 14 3).isSatisfiableInt :=
  unsat_of_sbc _ _
    (_root_.Schur.schur_sbc_is_symmetry_breaking 14 3 (by decide) (by decide)
      (_root_.Schur.schurTriples 14))
    PB.SchurSBC.sb_schur_3_14_unsat

/-- **End-to-end `S(2) < 5` via full value precedence.** Same UNSAT result, but the SBC is the
    Law–Lee `value_precedence` constraint (the full colour-symmetry break, not just `x₀ = 0`),
    proven a `domainSymmetryBreakingConstraint` and discharged through `unsat_of_domain_sbc`. -/
theorem schur_2_5_unsat_via_value_precedence : ¬ (_root_.Schur.schur_csp 5 2).isSatisfiableInt :=
  _root_.Schur.schur_unsat_of_value_precedence 5 2 (_root_.Schur.schurTriples 5)
    PB.SchurVP.schur_2_5_vp_unsat

end CSP.L2S.EndToEnd.Schur
