import Lean
import CSP.L2S.Backends.PB.Core

namespace CSP.L2S.PB

/-!
# PB backend — the `csp_reflect_unsat` command

PLAN.md §9, the CI-reproducible `_from_files` variant.

Given a constraint array `cs : Array Sat.PB.Constr`, a variable count, and the
path to a pre-generated VeriPB **kernel** proof, this command registers a
theorem `name : formulaUnsat cs` by running PBLean's verified reflection checker
(`checkProofBool`) on the proof via `native_decide` and applying
`checkProof_sound`.  No external solver runs at build time — only the committed
proof file is needed — so the result is CI-reproducible (the full shell-out
`csp_decide`, which invokes RoundingSat + veripb at elaboration, is a follow-up).

The trust base is PBLean's checker + Lean's kernel + the `native_decide`
reflection axiom (`Lean.ofReduceBool`); RoundingSat/veripb and the `.pbp` file
stay outside it — a wrong proof makes `checkProofBool` return `false` and the
command fails to elaborate.

Adapted from PBLean's `independent_set_reflect`. -/

open Lean Lean.Elab Lean.Elab.Command Lean.Meta

/-- `csp_reflect_unsat name cs numVars "proof.pbp"` registers
    `name : VeriPB.Reflect.formulaUnsat cs` from a committed VeriPB kernel proof,
    checked by PBLean's reflection checker via `native_decide`. -/
elab "csp_reflect_unsat " name:ident ppSpace cs:term:max ppSpace
    numVars:term:max ppSpace proofFile:str : command => do
  let declName := (← getCurrNamespace) ++ name.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let csExpr ← Term.elabTerm cs (some (mkApp (mkConst ``Array [.zero]) (mkConst ``Sat.PB.Constr)))
    let csExpr ← instantiateMVars csExpr
    let numVarsExpr ← Term.elabTerm numVars (some (mkConst ``Nat))
    let numVarsExpr ← instantiateMVars numVarsExpr
    let proofStr ← IO.FS.readFile proofPath
    let proofStrExpr := mkStrLit proofStr
    -- the Boolean check, compiled for native evaluation
    let checkExpr := mkApp3 (mkConst ``VeriPB.Reflect.checkProofBool)
      csExpr numVarsExpr proofStrExpr
    let auxName := declName ++ `check
    addAndCompile <| .defnDecl {
      name := auxName, levelParams := [], type := mkConst ``Bool,
      value := checkExpr, hints := .abbrev, safety := .safe }
    let auxConst := mkConst auxName
    let rflPrf := mkApp2 (mkConst ``Eq.refl [.succ .zero]) (mkConst ``Bool)
      (mkApp (mkConst ``Lean.reduceBool) auxConst)
    let hEqTrue := mkApp3 (mkConst ``Lean.ofReduceBool) auxConst (mkConst ``Bool.true) rflPrf
    -- checkProof_sound : checkProofBool … = true → formulaUnsat cs
    let unsatProof := mkApp4 (mkConst ``VeriPB.Reflect.checkProof_sound)
      csExpr numVarsExpr proofStrExpr hEqTrue
    let finalType := mkApp (mkConst ``VeriPB.Reflect.formulaUnsat) csExpr
    addDecl <| Declaration.thmDecl {
      name := declName, levelParams := [], type := finalType, value := unsatProof }
    logInfo m!"Registered {declName} : formulaUnsat (PBLean reflection)"

end CSP.L2S.PB
