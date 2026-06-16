import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.SchurSB

namespace CSP.L2S.PB.SchurSBC

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for the *symmetry-broken* Schur `S(2) < 5`

`Schur.extended_schur 5 _ 2` is the Schur CSP `schur_sb 5 2` (`{1,…,5}` 2-coloured with
colours `{0,1}`, no monochromatic `x + y = z`) **extended with the verified colour-fixing
symmetry-breaking constraint** `equals_const x₀ 0` (`Schur.schur_sb_constraint`, proved a
domain symmetry-breaking constraint in `Proofs/SchurSB.lean`).

Adding the SBC keeps the problem UNSAT (`S(2) = 4`), and the generic encoder discharges the
extra `equals_const` facet, so the proof is one `csp_unsat_file` over the committed certificate
`certs/schur_2_5_sbc.pbp`.  The *end-to-end* theorem `¬ (schur_sb 5 2).isSatisfiableInt`
(recovering UNSAT of the **original** problem from this extended UNSAT via the verified SBC)
is assembled in `CSP/L2S/EndToEnd/Schur.lean`.
-/

/-- The Schur `S(2) < 5` CSP extended with the colour-fixing SBC `x₀ = 0`. -/
def extended_schur_2_5 : IntCSP := Schur.extended_schur 5 (by decide) 2

/-- **Symmetry-broken `S(2) < 5`: `{1,…,5}` has no sum-free 2-colouring with `x₀` fixed.** -/
theorem extended_schur_2_5_unsat : ¬ extended_schur_2_5.isSatisfiableInt :=
  csp_unsat_file extended_schur_2_5 5 "certs/schur_2_5_sbc.pbp"

/-- The Schur `S(3) < 14` CSP extended with the colour-fixing SBC `x₀ = 0`. -/
def extended_schur_3_14 : IntCSP := Schur.extended_schur 14 (by decide) 3

/-- **Symmetry-broken `S(3) < 14`: `{1,…,14}` has no sum-free 3-colouring with `x₀` fixed.** -/
theorem extended_schur_3_14_unsat : ¬ extended_schur_3_14.isSatisfiableInt :=
  csp_unsat_file extended_schur_3_14 28 "certs/schur_3_14_sbc.pbp"

end CSP.L2S.PB.SchurSBC
