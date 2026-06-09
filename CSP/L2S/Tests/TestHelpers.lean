import Lean
import CSP.L2S.Core
import CSP.L2S.Translate

namespace CSP.L2S.Tests

open Lean Elab Term
open CSP.L2S

/-!
# Test Helpers for Multi-Backend Translation

Auto-generates MiniZinc and SMT-LIB from test files using compile-time filename detection.
-/

elab "fileName%" : term => do
  let fileName ← getFileName
  return mkStrLit fileName

def saveToFile (path : String) (content : String) : IO Unit := do
  let fp := System.FilePath.mk path
  if let some parent := fp.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path content
  IO.println s!"  → {path}"

def extractBasename (fullPath : String) : String :=
  let fp := System.FilePath.mk fullPath
  fp.fileStem.getD "unknown"

def saveBackend (basename : String) (csp : IntCSP) (backend : BackendType) : IO Unit := do
  let dirName := getBackendDirName backend
  let ext := getBackendExtension backend

  let content := translateTo csp backend
  saveToFile s!"CSP/L2S/Tests/{dirName}/{basename}.{ext}" content

def saveAllBackends (basename : String) (csp : IntCSP) : IO Unit := do
  IO.println s!"Translating {basename}..."
  for backend in allBackends do
    saveBackend basename csp backend

macro "saveAllBackendsAuto" csp:term : doElem =>
  `(doElem| do
    let fullPath : String := fileName%
    let basename := extractBasename fullPath
    saveAllBackends basename $csp
  )

end CSP.L2S.Tests
