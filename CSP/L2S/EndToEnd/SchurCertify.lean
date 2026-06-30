import CSP.L2S.Witness
import CSP.L2S.Proofs.SchurValuePrecedence
import CSP.L2S.Backends.PB.Problems.SchurVP

/-!
# Certifying Schur numbers up to S(4) — at the CSP level, both directions

Each Schur number is pinned by two CSP-level facts about the **original simple** CSP
`Schur.schur_sb n c` (bounds + sum-free triples, *no* symmetry breaking):

* a **lower bound** `S(c) ≥ n` = `(schur_sb n c).isSatisfiableInt`, from an external
  MiniZinc colouring witness re-checked in the Lean kernel by `decide` (`csp_sat_file`);
* an **upper bound** `S(c) < n+1` = `¬ (schur_sb (n+1) c).isSatisfiableInt`, from a verified
  pseudo-Boolean UNSAT certificate (`csp_unsat_file`).

Both legs run through the **same** symmetry-breaking constraint — Law–Lee
`value_precedence c` — proved equisatisfiable for the Schur CSP in
`Proofs/SchurValuePrecedence.lean`.  The SBC-extended instance appears only inside each
proof; every theorem below is stated about the *plain* `schur_sb`:

* lower bounds lift the witness via `Schur.schur_vp_equisatisfiability'` (`.mpr`);
* upper bounds lift the certificate via `Schur.schur_unsat_of_value_precedence`.

`S(2) = 4` and `S(3) = 13` are pinned exactly (both directions kernel-checked).  `S(4)`
has its lower bound `≥ 44` kernel-checked here; its upper bound `< 45` is the hard case
(the vp certificate is ~100 MB, far beyond the `native_decide` reach) — see
`docs/SCHUR_EXACT.md`.
-/

open CSP.L2S

namespace CSP.L2S.EndToEnd.SchurCertify

-- ============================================================================
-- Lower bounds (SAT): MiniZinc witness → kernel `decide` → lift via vp equisat
-- ============================================================================

/-- **`S(2) ≥ 4`.** -/
theorem schur_2_lb : (Schur.schur_sb 4 2).isSatisfiableInt :=
  (Schur.schur_vp_equisatisfiability' 4 2).mpr
    (csp_sat_file ((Schur.schur_sb 4 2).addConstraint (value_precedence 2))
      "CSP/L2S/EndToEnd/sols/schur_c2_n4.sol")

/-- **`S(3) ≥ 13`.** -/
theorem schur_3_lb : (Schur.schur_sb 13 3).isSatisfiableInt :=
  (Schur.schur_vp_equisatisfiability' 13 3).mpr
    (csp_sat_file ((Schur.schur_sb 13 3).addConstraint (value_precedence 3))
      "CSP/L2S/EndToEnd/sols/schur_c3_n13.sol")

set_option maxRecDepth 10000 in
/-- **`S(4) ≥ 44`.** -/
theorem schur_4_lb : (Schur.schur_sb 44 4).isSatisfiableInt :=
  (Schur.schur_vp_equisatisfiability' 44 4).mpr
    (csp_sat_file ((Schur.schur_sb 44 4).addConstraint (value_precedence 4))
      "CSP/L2S/EndToEnd/sols/schur_c4_n44.sol")

-- ============================================================================
-- Upper bounds (UNSAT): vp certificate → native_decide → lift via vp SBC
-- ============================================================================

/-- **`S(2) < 5`.** -/
theorem schur_2_ub : ¬ (Schur.schur_sb 5 2).isSatisfiableInt :=
  Schur.schur_unsat_of_value_precedence 5 2 (Schur.schurTriples 5)
    PB.SchurVP.schur_2_5_vp_unsat

/-- **`S(3) < 14`.** -/
theorem schur_3_ub : ¬ (Schur.schur_sb 14 3).isSatisfiableInt :=
  Schur.schur_unsat_of_value_precedence 14 3 (Schur.schurTriples 14)
    PB.SchurVP.schur_3_14_vp_unsat

-- `schur_4_ub : ¬ (Schur.schur_sb 45 4).isSatisfiableInt` is added once/if a
-- kernel-checkable vp certificate for n=45 is obtained (see scripts/schur_exact/shrink_s4.py
-- and docs/SCHUR_EXACT.md).  The instance solves (~46 s) but its certificate is ~100 MB.

-- ============================================================================
-- Exact values (both directions)
-- ============================================================================

/-- **`S(2) = 4`.** -/
theorem schur_2_exact :
    (Schur.schur_sb 4 2).isSatisfiableInt ∧ ¬ (Schur.schur_sb 5 2).isSatisfiableInt :=
  ⟨schur_2_lb, schur_2_ub⟩

/-- **`S(3) = 13`.** -/
theorem schur_3_exact :
    (Schur.schur_sb 13 3).isSatisfiableInt ∧ ¬ (Schur.schur_sb 14 3).isSatisfiableInt :=
  ⟨schur_3_lb, schur_3_ub⟩

end CSP.L2S.EndToEnd.SchurCertify
