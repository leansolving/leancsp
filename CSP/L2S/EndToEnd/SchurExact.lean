import CSP.L2S.Witness
import CSP.L2S.Proofs.SchurColorable
import CSP.L2S.EndToEnd.Schur

/-!
# End-to-end exact Schur numbers — both directions, fully kernel-checked

This module closes the loop on the Schur problem by combining the project's two
independent verification pipelines:

* **Lower bounds** (`S(c) ≥ n`) come from an *external solver witness*: a colouring is
  found outside Lean, committed to `sols/*.sol`, and re-checked in the **Lean kernel** by
  `csp_sat_file` (`Witness.lean`) → equisatisfiability (`schur_sb_equisatisfiability'`) →
  the math bridge (`schur_csp_iff_colorable`).  The solver is untrusted; this direction
  uses no `native_decide`, so the lower-bound theorems are **axiom-clean**.

* **Upper bounds** (`S(c) < n+1`, i.e. `¬ SchurColorable (n+1) c`) come from the verified
  **PB-UNSAT** pipeline (`EndToEnd/Schur.lean`'s `schur_2_5_unsat` / `schur_3_14_unsat`,
  kernel-checked pseudo-Boolean certificates) pushed through the same bridge.

Together they pin the **exact** values `S(2) = 4` and `S(3) = 13` (weak-Schur convention,
`x + y = z` with `x = y` allowed): `{1,…,n}` is colourable but `{1,…,n+1}` is not.
`S(4) ≥ 44` is included as a lower-bound-only demo (no PB-UNSAT for `S(4) < 45` exists
here — that instance is far too large to certify).
-/

open CSP.L2S

namespace CSP.L2S.EndToEnd.SchurExact

-- ============================================================================
-- Lower bounds (external witness, kernel `decide`)
-- ============================================================================

/-- **`S(2) ≥ 4`.** `{1,2,3,4}` is 2-colourable sum-free. -/
theorem S2_ge_4 : _root_.Schur.SchurColorable 4 2 :=
  (_root_.Schur.schur_csp_iff_colorable 4 2).mp
    ((_root_.Schur.schur_sb_equisatisfiability' 4 2 (by decide) (by decide)).mpr
      (csp_sat_file (_root_.Schur.schur_sb 4 (by decide) 2)
        "CSP/L2S/EndToEnd/sols/schur_c2_n4.sol"))

/-- **`S(3) ≥ 13`.** `{1,…,13}` is 3-colourable sum-free. -/
theorem S3_ge_13 : _root_.Schur.SchurColorable 13 3 :=
  (_root_.Schur.schur_csp_iff_colorable 13 3).mp
    ((_root_.Schur.schur_sb_equisatisfiability' 13 3 (by decide) (by decide)).mpr
      (csp_sat_file (_root_.Schur.schur_sb 13 (by decide) 3)
        "CSP/L2S/EndToEnd/sols/schur_c3_n13.sol"))

set_option maxRecDepth 10000 in
/-- **`S(4) ≥ 44`.** `{1,…,44}` is 4-colourable sum-free (lower-bound demo). -/
theorem S4_ge_44 : _root_.Schur.SchurColorable 44 4 :=
  (_root_.Schur.schur_csp_iff_colorable 44 4).mp
    ((_root_.Schur.schur_sb_equisatisfiability' 44 4 (by decide) (by decide)).mpr
      (csp_sat_file (_root_.Schur.schur_sb 44 (by decide) 4)
        "CSP/L2S/EndToEnd/sols/schur_c4_n44.sol"))

-- ============================================================================
-- Upper bounds (verified PB-UNSAT, via the same bridge)
-- ============================================================================

/-- **`S(2) < 5`.** `{1,…,5}` is *not* 2-colourable sum-free (from PB-UNSAT). -/
theorem not_S5_2 : ¬ _root_.Schur.SchurColorable 5 2 :=
  mt (_root_.Schur.schur_csp_iff_colorable 5 2).mpr
    CSP.L2S.EndToEnd.Schur.schur_2_5_unsat

/-- **`S(3) < 14`.** `{1,…,14}` is *not* 3-colourable sum-free (from PB-UNSAT). -/
theorem not_S14_3 : ¬ _root_.Schur.SchurColorable 14 3 :=
  mt (_root_.Schur.schur_csp_iff_colorable 14 3).mpr
    CSP.L2S.EndToEnd.Schur.schur_3_14_unsat

-- ============================================================================
-- Exact Schur numbers (both directions combined)
-- ============================================================================

/-- **`S(2) = 4`.** `{1,2,3,4}` is 2-colourable sum-free, but `{1,…,5}` is not. -/
theorem S2_eq_4 : _root_.Schur.SchurColorable 4 2 ∧ ¬ _root_.Schur.SchurColorable 5 2 :=
  ⟨S2_ge_4, not_S5_2⟩

/-- **`S(3) = 13`.** `{1,…,13}` is 3-colourable sum-free, but `{1,…,14}` is not. -/
theorem S3_eq_13 : _root_.Schur.SchurColorable 13 3 ∧ ¬ _root_.Schur.SchurColorable 14 3 :=
  ⟨S3_ge_13, not_S14_3⟩

end CSP.L2S.EndToEnd.SchurExact
