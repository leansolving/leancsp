import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.SchurSB

namespace CSP.L2S.PB.SchurVP

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — verified UNSAT for the *value-precedence*-extended Schur `S(2) < 5`

The Schur CSP `schur_sb 5 2` extended with the full Law–Lee `value_precedence 2` constraint.
The generic encoder emits its sound **staircase** relaxation `xⱼ ≤ j` (verified by
`value_precedence_staircase`), so the certificate genuinely carries the extra symmetry-breaking
constraints (unlike a dropped `if_then_or`).  The end-to-end theorem on the *original* Schur CSP
is assembled in `CSP/L2S/EndToEnd/Schur.lean` via `Schur.schur_unsat_of_value_precedence`.
-/

/-- The Schur `S(2) < 5` CSP extended with the value-precedence SBC. -/
def schur_2_5_vp : IntCSP := (Schur.schur_sb 5 2).addConstraint (value_precedence 2)

/-- **Value-precedence-extended `S(2) < 5` is UNSAT.** -/
theorem schur_2_5_vp_unsat : ¬ schur_2_5_vp.isSatisfiableInt :=
  csp_unsat_file schur_2_5_vp 5 "certs/schur_2_5_vp.pbp"

end CSP.L2S.PB.SchurVP
