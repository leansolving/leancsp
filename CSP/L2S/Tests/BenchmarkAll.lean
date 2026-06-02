import CSP.L2S.Core
import CSP.L2S.Tests.TestHelpersTimed

/-!
# Benchmark All Test Files

Runs all test files with timing measurements and generates comprehensive CSV output.

## CSV Format

The output CSV contains:
- problem_name: Test problem name
- backend: MiniZinc or SMT-LIB
- translation_ns: Pure translation time (nanoseconds)
- file_io_ms: File writing time (milliseconds)
- csv_append_ms: CSV append time (milliseconds)
- infrastructure_ms: Lean infrastructure overhead (milliseconds)
- total_ms: Total wall-clock time (milliseconds)
- file_size_bytes: Generated file size
-/

namespace CSP.L2S.Tests.Benchmark

open CSP.L2S.Tests.Timed

-- ============================================================================
-- CSV Record Structures
-- ============================================================================

/-- Raw timing record from test files -/
structure RawTimingRecord where
  problem_name : String
  backend : String
  translation_ns : Nat
  file_io_ns : Nat
  csv_append_ns : Nat
  file_size_bytes : Nat
  deriving Repr

/-- Enriched timing record with infrastructure overhead -/
structure EnrichedTimingRecord where
  problem_name : String
  backend : String
  translation_ns : Nat
  file_io_ns : Nat
  csv_append_ns : Nat
  infrastructure_ns : Nat
  total_ns : Nat
  file_size_bytes : Nat
  deriving Repr

/-- Convert enriched record to CSV row -/
def EnrichedTimingRecord.toCSVRow (record : EnrichedTimingRecord) : String :=
  s!"{record.problem_name},{record.backend},{record.translation_ns},{record.file_io_ns},{record.csv_append_ns},{record.infrastructure_ns},{record.total_ns},{record.file_size_bytes}"

/-- CSV header for enriched timing data -/
def enrichedCSVHeader : String :=
  "problem_name,backend,translation_ns,file_io_ns,csv_append_ns,infrastructure_ns,total_ns,file_size_bytes"

-- ============================================================================
-- CSV Parsing and Writing
-- ============================================================================

/-- Parse a CSV row into a RawTimingRecord -/
def parseRawCSVRow (row : String) : Option RawTimingRecord := do
  let fields := row.splitOn ","
  if fields.length != 6 then
    none
  else
    let problem_name := fields[0]!
    let backend := fields[1]!
    let translation_ns ← fields[2]!.toNat?
    let file_io_ns ← fields[3]!.toNat?
    let csv_append_ns ← fields[4]!.toNat?
    let file_size_bytes ← fields[5]!.toNat?
    some {
      problem_name, backend, translation_ns, file_io_ns,
      csv_append_ns, file_size_bytes
    }

/-- Read last N records from raw CSV -/
def readLastRawRecords (csvPath : String) (n : Nat) : IO (List RawTimingRecord) := do
  let fileExists ← System.FilePath.pathExists csvPath
  if !fileExists then
    return []

  let content ← IO.FS.readFile csvPath
  let lines := content.splitOn "\n"
  let dataLines := lines.filter (fun line => line != "" && !line.startsWith "problem_name")
  let lastN := dataLines.reverse.take n |>.reverse

  return lastN.filterMap parseRawCSVRow

/-- Write enriched record to final CSV -/
def appendEnrichedToCSV (csvPath : String) (record : EnrichedTimingRecord) : IO Unit := do
  let fileExists ← System.FilePath.pathExists csvPath

  let fp := System.FilePath.mk csvPath
  if let some parent := fp.parent then
    IO.FS.createDirAll parent

  let handle ← IO.FS.Handle.mk csvPath IO.FS.Mode.append

  if !fileExists then
    handle.putStrLn enrichedCSVHeader

  handle.putStrLn record.toCSVRow

/-- Path to the final enriched CSV file -/
def enrichedCSVPath : String := "CSP/L2S/Tests/timing_results.csv"

-- ============================================================================
-- Benchmarking
-- ============================================================================

/-- Run a Lean test file and measure wall-clock time -/
def runTest (filename : String) : IO (Bool × Nat) := do
  let leanFile := s!"CSP/L2S/Tests/lean/{filename}"
  let baseName := filename.dropRight 5  -- Remove ".lean"

  IO.print s!"[{baseName}] "

  -- Measure wall-clock time for the entire test execution
  let t₀ ← IO.monoMsNow

  -- Run: lake env lean --run <file>
  let output ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", leanFile]
  }

  let t₁ ← IO.monoMsNow
  let wallClockMs := t₁ - t₀

  if output.exitCode != 0 then
    IO.println "❌ FAILED"
    IO.eprintln s!"  Error: {output.stderr}"
    pure (false, wallClockMs)
  else
    IO.println s!"✓ ({wallClockMs}ms)"
    pure (true, wallClockMs)

/-- Process raw records and write enriched records with infrastructure overhead -/
def enrichAndWrite (rawRecords : List RawTimingRecord) (totalWallClockMs : Nat) : IO Unit := do
  if rawRecords.isEmpty then
    return

  -- Convert wall clock from milliseconds to nanoseconds
  let totalWallClockNs := totalWallClockMs * 1000000

  -- Total measured time from raw records (in nanoseconds)
  let measuredNs := rawRecords.foldl (fun acc r =>
    acc + r.translation_ns + r.file_io_ns + r.csv_append_ns) 0

  -- Infrastructure overhead = wall clock - measured (in nanoseconds)
  -- Divide equally among all backends (each test file generates 2 records: MiniZinc + SMT-LIB)
  let numBackends := rawRecords.length
  let totalInfrastructureNs := if totalWallClockNs > measuredNs then
    totalWallClockNs - measuredNs
  else
    0
  let infrastructureNsPerBackend := totalInfrastructureNs / numBackends

  -- Write enriched records
  for raw in rawRecords do
    let totalNs := raw.translation_ns + raw.file_io_ns + raw.csv_append_ns + infrastructureNsPerBackend
    let enriched : EnrichedTimingRecord := {
      problem_name := raw.problem_name
      backend := raw.backend
      translation_ns := raw.translation_ns
      file_io_ns := raw.file_io_ns
      csv_append_ns := raw.csv_append_ns
      infrastructure_ns := infrastructureNsPerBackend
      total_ns := totalNs
      file_size_bytes := raw.file_size_bytes
    }
    appendEnrichedToCSV enrichedCSVPath enriched

-- Get all .lean files from the lean directory using ls command
def getAllLeanFiles : IO (List String) := do
  let leanDir := "CSP/L2S/Tests/lean"

  -- Use ls to list files
  let output ← IO.Process.output {
    cmd := "ls"
    args := #["-1", leanDir]
  }

  if output.exitCode != 0 then
    IO.eprintln s!"Error listing directory: {output.stderr}"
    return []

  -- Filter for .lean files and sort
  let allFiles := output.stdout.splitOn "\n"
  let leanFiles := allFiles.filter (·.endsWith ".lean")
  return leanFiles.filter (· != "")  -- Remove empty strings

def main : IO Unit := do
  IO.println "======================================================================="
  IO.println "L2S Translation Benchmark - All Test Files"
  IO.println "======================================================================="
  IO.println ""

  -- Clear previous timing results
  let rawCSVPath := timingCSVPath
  let finalCSVPath := enrichedCSVPath

  let rawExists ← System.FilePath.pathExists rawCSVPath
  if rawExists then
    IO.FS.removeFile rawCSVPath
    IO.println s!"Cleared previous raw results from {rawCSVPath}"

  let finalExists ← System.FilePath.pathExists finalCSVPath
  if finalExists then
    IO.FS.removeFile finalCSVPath
    IO.println s!"Cleared previous final results from {finalCSVPath}"

  IO.println s!"Raw timing data: {rawCSVPath}"
  IO.println s!"Final results: {finalCSVPath}"
  IO.println ""

  -- Discover all .lean files
  let leanFiles ← getAllLeanFiles
  IO.println s!"Found {leanFiles.length} test files"
  IO.println ""

  -- Benchmark each file
  let mut successCount := 0
  let mut failCount := 0
  let startTime ← IO.monoMsNow

  for file in leanFiles do
    -- Run test and measure wall-clock time
    let (success, wallClockMs) ← runTest file

    if success then
      successCount := successCount + 1

      -- Read the raw records generated by this test (2 records: MiniZinc + SMT-LIB)
      let rawRecords ← readLastRawRecords rawCSVPath 2

      -- Enrich with infrastructure overhead and write to final CSV
      enrichAndWrite rawRecords wallClockMs
    else
      failCount := failCount + 1

  let endTime ← IO.monoMsNow
  let totalTime := endTime - startTime

  IO.println ""
  IO.println "======================================================================="
  IO.println "Benchmark Summary"
  IO.println "======================================================================="
  IO.println s!"Total files:    {leanFiles.length}"
  IO.println s!"Successful:     {successCount}"
  IO.println s!"Failed:         {failCount}"
  IO.println s!"Total time:     {totalTime}ms ({totalTime / 1000}s)"
  if successCount > 0 then
    IO.println s!"Avg per file:   {totalTime / leanFiles.length}ms"
  IO.println ""
  IO.println s!"Raw timing data: {rawCSVPath}"
  IO.println s!"Final results: {finalCSVPath}"
  IO.println ""
  IO.println "CSV Columns (all times in nanoseconds):"
  IO.println "  - translation_ns: Pure translation time"
  IO.println "  - file_io_ns: File writing time"
  IO.println "  - csv_append_ns: CSV append time"
  IO.println "  - infrastructure_ns: Lean overhead (Lake, imports, compilation, OS)"
  IO.println "  - total_ns: Total wall-clock time"
  IO.println ""
  IO.println "Note: infrastructure_ns = total_ns - (translation_ns + file_io_ns + csv_append_ns)"
  IO.println ""
  IO.println "To analyze results:"
  IO.println "  1. Open timing_results.csv in a spreadsheet"
  IO.println s!"  2. Command-line: column -t -s, {finalCSVPath} | less"
  IO.println "  3. Python analysis: python3 analyze_timing_results.py"

end CSP.L2S.Tests.Benchmark

-- Top-level main function for --run
def main : IO Unit := CSP.L2S.Tests.Benchmark.main
