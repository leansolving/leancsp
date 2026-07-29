import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.SchurSB

/-!
# Cautionary example: the strict reversal leader makes Schur `S(3)` wrongly UNSAT

`base13` is the 3-colour Schur CSP on `{1,…,13}` (satisfiable — `S(3) = 13`); every one of
its solutions is a palindrome.  `aug13` adds the strict lexicographic reversal leader
`x <_lex rev(x)`, which no palindrome satisfies, so `aug13` is UNSAT.  Certifying that
UNSAT through the verified PB pipeline yields a concrete false certificate; combined with
`base13` being SAT it shows the leader is *not* a valid symmetry-breaking constraint
(see `CSP/L2S/Proofs/SchurReversalCounterexample.lean`).
-/

namespace CSP.L2S.PB.SchurLexLeader

open CSP.L2S CSP.L2S.PB

/-- Base 3-colour Schur CSP at `n = 13` (satisfiable; all solutions palindromes). -/
def base13 : IntCSP := Schur.schur_csp_triples 13 3 (Schur.schurTriples 13)

/-- The strict lexicographic reversal leader over the 13 variables. -/
def leader : IntConstraint base13.num_vars := IntConstraint.strictLexRevLeader

/-- `base13` augmented with the reversal leader (UNSAT — no palindrome satisfies the leader). -/
def aug13 : IntCSP := base13.addConstraint leader

/-- **The augmented Schur CSP is UNSAT** (kernel-checked PB certificate) — the false
    certificate: adding the strict reversal leader wrongly rules out every one of
    `S(3) = 13`'s colourings. -/
theorem aug13_unsat : ¬ aug13.isSatisfiableInt :=
  csp_unsat_file aug13 27 "certs/schur_lex_13.pbp"

end CSP.L2S.PB.SchurLexLeader
