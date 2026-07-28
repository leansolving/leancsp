import CSP.L2S.Witness
import CSP.L2S.Proofs.SchurValuePrecedence
import CSP.L2S.Backends.PB.Problems.SchurVP

/-!
# Certifying Schur numbers up to S(4) — at the CSP level, both directions

Each Schur number is pinned by two CSP-level facts about the **original simple** CSP
`Schur.schur_csp n c` (bounds + sum-free triples, *no* symmetry breaking):

* a **lower bound** `S(c) ≥ n` = `(schur_csp n c).isSatisfiableInt`, from an external
  MiniZinc colouring witness re-checked in the Lean kernel by `decide` (`csp_sat_file`);
* an **upper bound** `S(c) < n+1` = `¬ (schur_csp (n+1) c).isSatisfiableInt`, from a verified
  pseudo-Boolean UNSAT certificate (`csp_unsat_file`).

Both legs run through the **same** symmetry-breaking constraint — Law–Lee
`value_precedence c` — proved equisatisfiable for the Schur CSP in
`Proofs/SchurValuePrecedence.lean`.  The SBC-extended instance appears only inside each
proof; every theorem below is stated about the *plain* `schur_csp`:

* lower bounds lift the witness via `Schur.schur_vp_equisatisfiability'` (`.mpr`);
* upper bounds lift the certificate via `Schur.schur_unsat_of_value_precedence`.

`S(2) = 4` and `S(3) = 13` are pinned exactly (both directions kernel-checked).  `S(4)`
has its lower bound `≥ 44` kernel-checked here; its upper bound `< 45` is the hard case
(the vp certificate is ~100 MB, far beyond the reach of the native reflection recheck) — see
`experiments/schur_exact/README.md`.
-/

open CSP.L2S

namespace CSP.L2S.EndToEnd.SchurCertify

-- ============================================================================
-- Lower bounds (SAT): MiniZinc witness → kernel `decide` → lift via vp equisat
-- ============================================================================

/-- **`S(2) ≥ 4`.** -/
theorem schur_2_lb : (Schur.schur_csp 4 2).isSatisfiableInt :=
  (Schur.schur_vp_equisatisfiability' 4 2).mpr
    (csp_sat_file ((Schur.schur_csp 4 2).addConstraint (value_precedence 2))
      "CSP/L2S/EndToEnd/sols/schur_c2_n4.sol")

/-- **`S(3) ≥ 13`.** -/
theorem schur_3_lb : (Schur.schur_csp 13 3).isSatisfiableInt :=
  (Schur.schur_vp_equisatisfiability' 13 3).mpr
    (csp_sat_file ((Schur.schur_csp 13 3).addConstraint (value_precedence 3))
      "CSP/L2S/EndToEnd/sols/schur_c3_n13.sol")

set_option maxRecDepth 10000 in
/-- **`S(4) ≥ 44`.** -/
theorem schur_4_lb : (Schur.schur_csp 44 4).isSatisfiableInt :=
  (Schur.schur_vp_equisatisfiability' 44 4).mpr
    (csp_sat_file ((Schur.schur_csp 44 4).addConstraint (value_precedence 4))
      "CSP/L2S/EndToEnd/sols/schur_c4_n44.sol")

-- ============================================================================
-- Upper bounds (UNSAT): vp certificate → ofReduceBool reflection → lift via vp SBC
-- ============================================================================

/-- **`S(2) < 5`.** -/
theorem schur_2_ub : ¬ (Schur.schur_csp 5 2).isSatisfiableInt :=
  Schur.schur_unsat_of_value_precedence 5 2 (Schur.schurTriples 5)
    PB.SchurVP.schur_2_5_vp_unsat

/-- **`S(3) < 14`.** -/
theorem schur_3_ub : ¬ (Schur.schur_csp 14 3).isSatisfiableInt :=
  Schur.schur_unsat_of_value_precedence 14 3 (Schur.schurTriples 14)
    PB.SchurVP.schur_3_14_vp_unsat

-- `S(4) = 44` (`schur_4_ub`, `schur_4_exact`) is at the end of this file, commented out — its
-- certificate is ~98 MB, too large to commit; enable it after generating the cert (see below).

-- ============================================================================
-- Exact values (both directions)
-- ============================================================================

/-- **`S(2) = 4`.** -/
theorem schur_2_exact :
    (Schur.schur_csp 4 2).isSatisfiableInt ∧ ¬ (Schur.schur_csp 5 2).isSatisfiableInt :=
  ⟨schur_2_lb, schur_2_ub⟩

/-- **`S(3) = 13`.** -/
theorem schur_3_exact :
    (Schur.schur_csp 13 3).isSatisfiableInt ∧ ¬ (Schur.schur_csp 14 3).isSatisfiableInt :=
  ⟨schur_3_lb, schur_3_ub⟩

-- ============================================================================
-- S(4) = 44 (disabled). The value-precedence certificate for n=45 is ~98 MB, too large to
-- commit. Generate it with `python experiments/run_schur_exact.py` (writes
-- `experiments/schur_exact/artifacts/schur_4_45_vp_kernel.pbp`), then remove the `/-` and `-/`
-- around the block below to enable `schur_4_ub` / `schur_4_exact`.
-- ============================================================================

/-
def schur_4_45_vp : IntCSP := (Schur.schur_csp 45 4).addConstraint (value_precedence 4)

set_option maxRecDepth 100000 in
theorem schur_4_45_vp_unsat : ¬ schur_4_45_vp.isSatisfiableInt :=
  csp_unsat_file schur_4_45_vp 135
    "../../../experiments/schur_exact/artifacts/schur_4_45_vp_kernel.pbp"

/-- **`S(4) < 45`.** -/
theorem schur_4_ub : ¬ (Schur.schur_csp 45 4).isSatisfiableInt :=
  Schur.schur_unsat_of_value_precedence 45 4 (Schur.schurTriples 45) schur_4_45_vp_unsat

/-- **`S(4) = 44`** — both directions. -/
theorem schur_4_exact :
    (Schur.schur_csp 44 4).isSatisfiableInt ∧ ¬ (Schur.schur_csp 45 4).isSatisfiableInt :=
  ⟨schur_4_lb, schur_4_ub⟩
-/

end CSP.L2S.EndToEnd.SchurCertify
