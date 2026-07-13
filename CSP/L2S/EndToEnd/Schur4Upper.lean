import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Proofs.SchurValuePrecedence
import CSP.L2S.Proofs.SchurSB
import CSP.L2S.EndToEnd.SchurCertify

/-!
# `S(4) < 45` kernel upper bound via a `readFile`-loaded 98 MB certificate

`csp_unsat_file` splices the certificate with `include_str`, which OOMs the Lean *parser*
on the ~98 MB S(4) certificate.  This module defines `csp_reflect_unsat_csp`, identical to
`cspUnsatReflect`'s reflection step except the certificate is read with `IO.FS.readFile` at
elaboration and turned into a `StrLit` `Expr` directly — so the parser never sees the 98 MB
literal.  The native evaluation (`checkProofBool`, what `ofReduceBool` reduces) is the exact
49 s call measured natively in `experiments/sbc/results/check_largest.csv`.

The command registers only the PB-level `formulaUnsat` cert; the CSP-level bridge (`csp_unsat`)
and the value-precedence lift are ordinary theorems below, exactly as for `schur_3_ub`.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term
open CSP.L2S CSP.L2S.PB

namespace CSP.L2S.PB

/-- `csp_reflect_unsat_csp name csp numVars "abs/path.pbp"` registers
    `name : VeriPB.Reflect.formulaUnsat ((cspSig csp).monotonicity ++ … |>.map PBConstr.toNatConstr)`
    from a committed VeriPB kernel proof read from disk at elaboration time (no `include_str`),
    discharged by the same hand-built `Lean.ofReduceBool` term as `cspUnsatReflect`. -/
elab "csp_reflect_unsat_csp " name:ident ppSpace csp:term:max ppSpace
    numVars:term:max ppSpace path:str : command => do
  let declName := (← getCurrNamespace) ++ name.getId
  let proofPath := path.getString
  liftTermElabM do
    let proofStr ← IO.FS.readFile proofPath
    logInfo m!"read {proofStr.length} bytes from {proofPath}"
    let certE := mkStrLit proofStr
    let csE ← instantiateMVars (← elabTerm
      (← `((((cspSig $csp).monotonicity ++ EncConstr.combine (encodeCSP $csp)).toArray.map
            PBConstr.toNatConstr)))
      (some (mkApp (Lean.mkConst ``Array [.zero]) (Lean.mkConst ``Sat.PB.Constr))))
    let numE ← instantiateMVars (← elabTerm numVars (some (Lean.mkConst ``Nat)))
    let auxName := declName ++ `check
    addAndCompile <| .defnDecl {
      name := auxName, levelParams := [], type := Lean.mkConst ``Bool
      value := mkApp3 (Lean.mkConst ``VeriPB.Reflect.checkProofBool) csE numE certE
      hints := .abbrev, safety := .safe }
    let auxConst := Lean.mkConst auxName
    let hEqTrue := mkApp3 (Lean.mkConst ``Lean.ofReduceBool) auxConst (Lean.mkConst ``Bool.true)
      (mkApp2 (Lean.mkConst ``Eq.refl [.succ .zero]) (Lean.mkConst ``Bool)
        (mkApp (Lean.mkConst ``Lean.reduceBool) auxConst))
    addDecl <| Declaration.thmDecl {
      name := declName, levelParams := []
      type := mkApp (Lean.mkConst ``VeriPB.Reflect.formulaUnsat) csE
      value := mkApp4 (Lean.mkConst ``VeriPB.Reflect.checkProof_sound) csE numE certE hEqTrue }
    logInfo m!"kernel-accepted {declName} : formulaUnsat"

end CSP.L2S.PB

namespace CSP.L2S.EndToEnd.SchurCertify

/-- The Schur `S(4) < 45` CSP extended with the value-precedence SBC. -/
def schur_4_45_vp : IntCSP := (Schur.schur_sb 45 4).addConstraint (value_precedence 4)

-- The ~98 MB certificate, read from disk (no `include_str`), reflected in the kernel.
-- The cert is too large to commit; regenerate it locally with the UNSAT pipeline via
-- `experiments/run_schur_exact.py` (see `experiments/schur_exact/README.md`).  Path is
-- relative to the package root (the `lake build` CWD), as `IO.FS.readFile` resolves it.
csp_reflect_unsat_csp schur_4_45_vp_cert schur_4_45_vp 135
  "experiments/schur_exact/artifacts/schur_4_45_vp_kernel.pbp"

set_option maxRecDepth 100000 in
/-- **Value-precedence-extended `S(4) < 45` is UNSAT.** -/
theorem schur_4_45_vp_unsat : ¬ schur_4_45_vp.isSatisfiableInt :=
  csp_unsat schur_4_45_vp schur_4_45_vp_cert

/-- **`S(4) < 45`.** -/
theorem schur_4_ub : ¬ (Schur.schur_sb 45 4).isSatisfiableInt :=
  Schur.schur_unsat_of_value_precedence 45 4 (Schur.schurTriples 45) schur_4_45_vp_unsat

/-- **`S(4) = 44`** — both directions, fully kernel-verified. -/
theorem schur_4_exact :
    (Schur.schur_sb 44 4).isSatisfiableInt ∧ ¬ (Schur.schur_sb 45 4).isSatisfiableInt :=
  ⟨schur_4_lb, schur_4_ub⟩

end CSP.L2S.EndToEnd.SchurCertify
