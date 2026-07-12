import Lean
import CSP.L2S.Backends.PB.Core
import CSP.L2S.Backends.PB.Serialize

namespace CSP.L2S.PB

/-!
# PB backend — the `csp_reflect_unsat` and `csp_decide` commands

Two ways to register `name : VeriPB.Reflect.formulaUnsat cs` from a pseudo-Boolean
UNSAT certificate, both discharging the kernel proof through PBLean's reflection
checker (`checkProofBool`) with a hand-built `Lean.ofReduceBool` term and
`checkProof_sound` (this is also the discharge `csp_unsat_file` now uses):

* **`csp_reflect_unsat name cs numVars "proof.pbp"`** (PLAN.md §9) reads a
  *committed* VeriPB kernel proof file.  No external solver runs at build time, so
  the result is **CI-reproducible** — this is the form used by every committed
  end-to-end UNSAT theorem.

* **`csp_decide name cs numVars`** is the *convenience* variant: it serializes `cs`
  to OPB at elaboration time (via the untrusted `Serialize.toOPBString`, run with
  `evalExpr`), shells out to **RoundingSat** (`--proof-log`) and **veripb**
  (`--elaborate`) to produce the kernel proof, then reflects it.  Requires both
  solvers on `PATH` at build time, so it is **not** hermetic — use it
  interactively to *generate* a certificate, then commit the kernel `.pbp` and
  switch to `csp_reflect_unsat` for reproducibility.

The trust base is identical for both: PBLean's checker + Lean's kernel + the
reflection axioms `Lean.ofReduceBool` / `Lean.trustCompiler`.  RoundingSat, veripb, the
serializer, and the `.opb`/`.pbp` files stay **outside** it — a wrong certificate
makes `checkProofBool` return `false` against the *Lean-side* `cs`, so the command
fails to elaborate rather than producing an unsound theorem.

Adapted from PBLean's `independent_set_reflect` / `independent_set_decide`. -/

open Lean Lean.Elab Lean.Elab.Command Lean.Meta

/-- Register `declName : VeriPB.Reflect.formulaUnsat csExpr` from a VeriPB kernel
    proof string, checked by PBLean's reflection checker and discharged by a hand-built
    `Lean.ofReduceBool` term.  Shared by both commands; the certificate `proofStr` is
    untrusted (a wrong one makes the `checkProofBool` reduction `false`, so the
    `Eq.refl` term fails to typecheck). -/
private def registerFormulaUnsat (declName : Name) (csExpr numVarsExpr : Expr)
    (proofStr : String) : TermElabM Unit := do
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

/-- Elaborate the shared `cs`/`numVars` arguments to `(Array Sat.PB.Constr, Nat)`
    expressions, instantiating metavariables. -/
private def elabUnsatArgs (cs numVars : Syntax) : TermElabM (Expr × Expr) := do
  let csExpr ← Term.elabTerm cs
    (some (mkApp (mkConst ``Array [.zero]) (mkConst ``Sat.PB.Constr)))
  let csExpr ← instantiateMVars csExpr
  let numVarsExpr ← Term.elabTerm numVars (some (mkConst ``Nat))
  let numVarsExpr ← instantiateMVars numVarsExpr
  return (csExpr, numVarsExpr)

/-- `csp_reflect_unsat name cs numVars "proof.pbp"` registers
    `name : VeriPB.Reflect.formulaUnsat cs` from a committed VeriPB kernel proof,
    checked by PBLean's reflection checker and discharged by a `Lean.ofReduceBool` term. -/
elab "csp_reflect_unsat " name:ident ppSpace cs:term:max ppSpace
    numVars:term:max ppSpace proofFile:str : command => do
  let declName := (← getCurrNamespace) ++ name.getId
  let proofPath := proofFile.getString
  liftTermElabM do
    let (csExpr, numVarsExpr) ← elabUnsatArgs cs numVars
    let proofStr ← IO.FS.readFile proofPath
    registerFormulaUnsat declName csExpr numVarsExpr proofStr
    logInfo m!"Registered {declName} : formulaUnsat (PBLean reflection)"

/-- Run an external command, throwing on non-zero exit; returns stdout. -/
private def runCmd (cmd : String) (args : Array String) (ctx : String) :
    IO String := do
  let r ← IO.Process.output { cmd := cmd, args := args }
  if r.exitCode != 0 then
    throw <| IO.userError
      s!"{ctx}: `{cmd}` failed (exit {r.exitCode})\nstderr:\n{r.stderr}\nstdout:\n{r.stdout}"
  return r.stdout

/-- Substring test (`pat` occurs in `s`). -/
private def strContains (s pat : String) : Bool := (s.splitOn pat).length > 1

/-- Serialize `cs` to OPB by compiling and running the untrusted serializer
    (`Serialize.toOPBString`) on the elaborated constraint array. -/
private unsafe def evalOPBUnsafe (csExpr numVarsExpr : Expr) : TermElabM String :=
  evalExpr String (mkConst ``String) (mkApp2 (mkConst ``toOPBString) csExpr numVarsExpr)

@[implemented_by evalOPBUnsafe]
private opaque evalOPB (csExpr numVarsExpr : Expr) : TermElabM String

/-- `csp_decide name cs numVars` serializes `cs` to OPB, runs RoundingSat + veripb
    at elaboration time, and registers `name : VeriPB.Reflect.formulaUnsat cs` from
    the resulting kernel proof.  **Not hermetic** — needs `roundingsat` and
    `veripb` on `PATH`.  See the module docstring; prefer `csp_reflect_unsat` for
    committed theorems. -/
elab "csp_decide " name:ident ppSpace cs:term:max ppSpace
    numVars:term:max : command => do
  let declName := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    let (csExpr, numVarsExpr) ← elabUnsatArgs cs numVars
    -- Serialize cs to OPB by evaluating the untrusted serializer at elaboration.
    let opb ← evalOPB csExpr numVarsExpr
    -- Scratch dir for the .opb / .pbp pipeline.
    let tmp := (← IO.Process.output { cmd := "mktemp", args := #["-d"] }).stdout.trimAscii.toString
    if tmp.isEmpty then throwError "csp_decide: mktemp returned an empty path"
    let opbPath := System.FilePath.mk s!"{tmp}/instance.opb"
    let augPath := s!"{tmp}/proof.pbp"
    let kernelPath := s!"{tmp}/kernel.pbp"
    let rm : IO Unit := do
      let _ ← IO.Process.output { cmd := "rm", args := #["-rf", tmp] }
    try
      IO.FS.writeFile opbPath opb
      let rsOut ← runCmd "roundingsat" #[opbPath.toString, s!"--proof-log={augPath}"]
        "RoundingSat"
      unless strContains rsOut "s UNSATISFIABLE" do
        throwError
          "csp_decide: RoundingSat did not report UNSATISFIABLE — the CSP may be \
           satisfiable, or the OPB was rejected.\nRoundingSat output:\n{rsOut}"
      let _ ← runCmd "veripb" #["--elaborate", kernelPath, opbPath.toString, augPath] "veripb"
      let proofStr ← IO.FS.readFile (System.FilePath.mk kernelPath)
      registerFormulaUnsat declName csExpr numVarsExpr proofStr
      rm
      logInfo m!"Registered {declName} : formulaUnsat (RoundingSat + veripb, ofReduceBool)"
    catch e =>
      rm
      throw e

end CSP.L2S.PB
