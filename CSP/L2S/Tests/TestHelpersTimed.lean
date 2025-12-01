import Lean
import CSP.L2S.Core
import CSP.L2S.Translate

namespace CSP.L2S.Tests.Timed

open Lean Elab Term
open CSP.L2S

/-!
# Timed Test Helpers

Measures translation time per backend and exports to CSV.
-/

def timeItNanos {α : Type} (action : IO α) : IO (α × Nat) := do
  let t₀ ← IO.monoNanosNow
  let result ← action
  let t₁ ← IO.monoNanosNow
  return (result, t₁ - t₀)

def timePureNanos {α : Type} (computation : Unit → α) : IO (α × Nat) := do
  let t₀ ← IO.monoNanosNow
  let result := computation ()
  let t₁ ← IO.monoNanosNow
  return (result, t₁ - t₀)

elab "fileName%" : term => do
  let fileName ← getFileName
  return mkStrLit fileName

def extractBasename (fullPath : String) : String :=
  let fp := System.FilePath.mk fullPath
  fp.fileStem.getD "unknown"

def saveToFile (path : String) (content : String) : IO Unit := do
  let fp := System.FilePath.mk path
  if let some parent := fp.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile path content

structure BackendTimings where
  backend_name : String
  translation_ns : Nat
  file_io_ns : Nat
  csv_append_ns : Nat
  file_size_bytes : Nat
  deriving Repr

structure TimingRecord where
  problem_name : String
  backend : String
  translation_ns : Nat
  file_io_ns : Nat
  csv_append_ns : Nat
  file_size_bytes : Nat
  deriving Repr

def TimingRecord.toCSVRow (record : TimingRecord) : String :=
  s!"{record.problem_name},{record.backend},{record.translation_ns},{record.file_io_ns},{record.csv_append_ns},{record.file_size_bytes}"

def csvHeader : String :=
  "problem_name,backend,translation_ns,file_io_ns,csv_append_ns,file_size_bytes"

def appendToCSV (csvPath : String) (record : TimingRecord) : IO Nat := do
  let t₀ ← IO.monoNanosNow
  let fileExists ← System.FilePath.pathExists csvPath
  let fp := System.FilePath.mk csvPath
  if let some parent := fp.parent then
    IO.FS.createDirAll parent
  let handle ← IO.FS.Handle.mk csvPath IO.FS.Mode.append
  if !fileExists then
    handle.putStrLn csvHeader
  handle.putStrLn record.toCSVRow
  let t₁ ← IO.monoNanosNow
  return (t₁ - t₀)

def timingCSVPath : String := "CSP/L2S/Tests/timing_results_raw.csv"

def saveBackendTimed (basename : String) (csp : HomogeneousCSP)
    (backend : BackendType) (prevCSVTime : Nat := 0) : IO BackendTimings := do
  let dirName := getBackendDirName backend
  let ext := getBackendExtension backend
  let filepath := s!"CSP/L2S/Tests/{dirName}/{basename}.{ext}"
  let backendName := getBackendName backend
  let (content, translateTimeNs) ← timePureNanos (fun _ => translateTo csp backend)
  let (_, ioTimeNs) ← timeItNanos (saveToFile filepath content)
  let fileSize := content.length
  let record : TimingRecord := {
    problem_name := basename
    backend := backendName
    translation_ns := translateTimeNs
    file_io_ns := ioTimeNs
    csv_append_ns := prevCSVTime
    file_size_bytes := fileSize
  }
  let csvAppendTimeNs ← appendToCSV timingCSVPath record

  return {
    backend_name := backendName
    translation_ns := translateTimeNs
    file_io_ns := ioTimeNs
    csv_append_ns := csvAppendTimeNs
    file_size_bytes := fileSize
  }

def saveAllBackendsTimed (basename : String) (csp : HomogeneousCSP) : IO Unit := do
  IO.println s!"Translating {basename}..."

  let mut totalTranslationNs := 0
  let mut totalIONs := 0
  let mut totalCSVNs := 0
  let mut totalSize := 0
  let mut prevCSVTime := 0

  for backend in allBackends do
    let timings ← saveBackendTimed basename csp backend prevCSVTime
    let ext := getBackendExtension backend
    let translateUs := timings.translation_ns / 1000
    let ioUs := timings.file_io_ns / 1000
    let csvUs := timings.csv_append_ns / 1000

    IO.println s!"  [{timings.backend_name}] Translation: {timings.translation_ns}ns ({translateUs}μs) | I/O: {timings.file_io_ns}ns ({ioUs}μs) | CSV: {timings.csv_append_ns}ns ({csvUs}μs) | Size: {timings.file_size_bytes} bytes"
    IO.println s!"    → CSP/L2S/Tests/{getBackendDirName backend}/{basename}.{ext}"

    totalTranslationNs := totalTranslationNs + timings.translation_ns
    totalIONs := totalIONs + timings.file_io_ns
    totalCSVNs := totalCSVNs + timings.csv_append_ns
    totalSize := totalSize + timings.file_size_bytes
    prevCSVTime := timings.csv_append_ns

  let totalTranslationUs := totalTranslationNs / 1000
  let totalIOUs := totalIONs / 1000
  let totalCSVUs := totalCSVNs / 1000
  IO.println s!"  [TOTAL] Translation: {totalTranslationNs}ns ({totalTranslationUs}μs) | I/O: {totalIONs}ns ({totalIOUs}μs) | CSV: {totalCSVNs}ns ({totalCSVUs}μs) | Total Size: {totalSize} bytes"
  IO.println s!"  Raw timing data appended to: {timingCSVPath}"

macro "saveAllBackendsAutoTimed" csp:term : doElem =>
  `(doElem| do
    let fullPath : String := fileName%
    let basename := extractBasename fullPath
    saveAllBackendsTimed basename $csp
  )

end CSP.L2S.Tests.Timed
