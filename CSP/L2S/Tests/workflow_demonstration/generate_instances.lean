import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Translate
import CSP.L2S.Backend

open CSP.L2S

/-!
# N-Queens Instance Generator for Workflow Demonstration

Generates N-Queens instances for sizes 10, 20, 30, ..., 150
to demonstrate translation vs solving time comparison.

Each instance is translated to both MiniZinc and SMT-LIB formats,
with timing data recorded for analysis.

## Multi-Run Benchmarking

To avoid outliers, each translation is measured multiple times:
- 1 warm-up run (discarded)
- 5 measured runs
- Statistics computed: mean, median, min, max

IMPORTANT: This file uses custom save functions to write files to
workflow_demonstration/mzn/ and workflow_demonstration/smt2/ instead of
the default Tests/ directories.
-/

-- ============================================================================
-- Configuration
-- ============================================================================

/-- Number of warm-up runs to discard -/
def WARMUP_RUNS : Nat := 1

/-- Number of measured runs for statistics -/
def MEASURED_RUNS : Nat := 5

-- ============================================================================
-- Statistical Helper Functions
-- ============================================================================

/-- Compute arithmetic mean of a list of Nat values -/
def listMean (xs : List Nat) : Float :=
  if xs.isEmpty then 0.0
  else xs.foldl (· + ·) 0 |>.toFloat / xs.length.toFloat

/-- Compute median of a list of Nat values -/
def listMedian (xs : List Nat) : Float :=
  let sorted := xs.mergeSort (· ≤ ·)
  let n := sorted.length
  if n == 0 then 0.0
  else if n % 2 == 1 then
    (sorted[n / 2]!).toFloat
  else
    ((sorted[n / 2 - 1]! + sorted[n / 2]!).toFloat) / 2.0

/-- Compute minimum of a list of Nat values -/
def listMin (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | h :: t => t.foldl min h

/-- Compute maximum of a list of Nat values -/
def listMax (xs : List Nat) : Nat :=
  xs.foldl max 0

-- ============================================================================
-- Benchmark Statistics Structure
-- ============================================================================

/-- Statistics from multiple benchmark runs -/
structure BenchmarkStats where
  runs : Nat           -- number of measured runs
  mean_ns : Float      -- arithmetic mean in nanoseconds
  median_ns : Float    -- median (robust to outliers)
  min_ns : Nat         -- minimum (fastest)
  max_ns : Nat         -- maximum (slowest)

/-- Compute statistics from a list of timing measurements -/
def computeStats (timings : List Nat) : BenchmarkStats :=
  { runs := timings.length
    mean_ns := listMean timings
    median_ns := listMedian timings
    min_ns := listMin timings
    max_ns := listMax timings }

-- ============================================================================
-- Timing Infrastructure
-- ============================================================================

/-- Timing record with statistics for CSV export -/
structure TimingRecordStats where
  problem_name : String
  backend : String
  warmup_runs : Nat
  measured_runs : Nat
  -- Translation statistics
  translate_mean_ns : Float
  translate_median_ns : Float
  translate_min_ns : Nat
  translate_max_ns : Nat
  -- File I/O statistics
  io_mean_ns : Float
  io_median_ns : Float
  io_min_ns : Nat
  io_max_ns : Nat
  -- File info
  file_size_bytes : Nat

/-- Convert timing record to CSV row -/
def TimingRecordStats.toCSVRow (r : TimingRecordStats) : String :=
  s!"{r.problem_name},{r.backend},{r.warmup_runs},{r.measured_runs},{r.translate_mean_ns},{r.translate_median_ns},{r.translate_min_ns},{r.translate_max_ns},{r.io_mean_ns},{r.io_median_ns},{r.io_min_ns},{r.io_max_ns},{r.file_size_bytes}"

/-- CSV header for timing records -/
def timingCSVHeader : String :=
  "problem_name,backend,warmup_runs,measured_runs,translate_mean_ns,translate_median_ns,translate_min_ns,translate_max_ns,io_mean_ns,io_median_ns,io_min_ns,io_max_ns,file_size_bytes"

/-- Time an IO action in nanoseconds -/
def timeItNanos (action : IO α) : IO (α × Nat) := do
  let t₀ ← IO.monoNanosNow
  let result ← action
  let t₁ ← IO.monoNanosNow
  return (result, t₁ - t₀)

/-- Time a pure computation in nanoseconds -/
def timePureNanos (f : Unit → α) : IO (α × Nat) := do
  let t₀ ← IO.monoNanosNow
  let result := f ()
  let t₁ ← IO.monoNanosNow
  return (result, t₁ - t₀)

/-- Save string to file -/
def saveToFile (filepath : String) (content : String) : IO Unit := do
  let fp := System.FilePath.mk filepath
  if let some parent := fp.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile fp content

-- ============================================================================
-- Multi-Run Timing Collection
-- ============================================================================

/-- Collect N timings after W warm-up runs (for pure computation) -/
def collectPureTimings (warmup runs : Nat) (f : Unit → α) : IO (List Nat) := do
  -- Warm-up runs (discarded)
  for _ in [:warmup] do
    let _ := f ()
  -- Measured runs
  let mut timings : List Nat := []
  for _ in [:runs] do
    let (_, dt) ← timePureNanos f
    timings := dt :: timings
  return timings.reverse

/-- Collect N timings after W warm-up runs (for IO actions) -/
def collectIOTimings (warmup runs : Nat) (action : IO α) : IO (List Nat) := do
  -- Warm-up runs (discarded)
  for _ in [:warmup] do
    let _ ← action
  -- Measured runs
  let mut timings : List Nat := []
  for _ in [:runs] do
    let (_, dt) ← timeItNanos action
    timings := dt :: timings
  return timings.reverse

-- ============================================================================
-- Custom Save Functions for Workflow Demonstration
-- ============================================================================

/-- Path to workflow demonstration CSV -/
def workflowTimingCSVPath : String := "CSP/L2S/Tests/workflow_demonstration/timing_results.csv"

/-- Base directory for workflow demonstration -/
def workflowBaseDir : String := "CSP/L2S/Tests/workflow_demonstration"

/-- Backend timings structure with statistics -/
structure BackendTimingsStats where
  backend_name : String
  translate_stats : BenchmarkStats
  io_stats : BenchmarkStats
  file_size_bytes : Nat

/-- Append timing record to CSV file (creates header if file doesn't exist) -/
def appendToCSVStats (csvPath : String) (record : TimingRecordStats) (writeHeader : Bool) : IO Unit := do
  let handle ← IO.FS.Handle.mk csvPath IO.FS.Mode.append
  if writeHeader then
    handle.putStrLn timingCSVHeader
  handle.putStrLn record.toCSVRow

/-- Save CSP to specific backend with multi-run timing -/
def saveBackendTimedMultiRun (basename : String) (csp : IntCSP)
    (backend : BackendType) (writeCSVHeader : Bool) : IO BackendTimingsStats := do
  let dirName := getBackendDirName backend
  let ext := getBackendExtension backend
  let filepath := s!"{workflowBaseDir}/{dirName}/{basename}.{ext}"
  let backendName := getBackendName backend

  -- Collect translation timings (pure computation)
  let translateTimings ← collectPureTimings WARMUP_RUNS MEASURED_RUNS (fun _ => translateTo csp backend)
  let translateStats := computeStats translateTimings

  -- Get final content for file I/O
  let content := translateTo csp backend
  let fileSize := content.length

  -- Collect file I/O timings
  let ioTimings ← collectIOTimings WARMUP_RUNS MEASURED_RUNS (saveToFile filepath content)
  let ioStats := computeStats ioTimings

  -- Export to CSV
  let record : TimingRecordStats := {
    problem_name := basename
    backend := backendName
    warmup_runs := WARMUP_RUNS
    measured_runs := MEASURED_RUNS
    translate_mean_ns := translateStats.mean_ns
    translate_median_ns := translateStats.median_ns
    translate_min_ns := translateStats.min_ns
    translate_max_ns := translateStats.max_ns
    io_mean_ns := ioStats.mean_ns
    io_median_ns := ioStats.median_ns
    io_min_ns := ioStats.min_ns
    io_max_ns := ioStats.max_ns
    file_size_bytes := fileSize
  }
  appendToCSVStats workflowTimingCSVPath record writeCSVHeader

  return {
    backend_name := backendName
    translate_stats := translateStats
    io_stats := ioStats
    file_size_bytes := fileSize
  }

/-- Format nanoseconds as a human-readable string with μs -/
def formatNanos (ns : Float) : String :=
  let μs := ns / 1000.0
  s!"{μs.round}μs"

/-- Save CSP to all backends with multi-run timing -/
def saveAllBackendsTimedMultiRun (basename : String) (csp : IntCSP) (isFirst : Bool) : IO Unit := do
  IO.println s!"Translating {basename} ({WARMUP_RUNS} warmup + {MEASURED_RUNS} runs)..."

  let mut writeHeader := isFirst
  for backend in allBackends do
    let timings ← saveBackendTimedMultiRun basename csp backend writeHeader
    let ext := getBackendExtension backend

    -- Show median (most robust) with min-max range
    let translateMedian := formatNanos timings.translate_stats.median_ns
    let translateMin := formatNanos timings.translate_stats.min_ns.toFloat
    let translateMax := formatNanos timings.translate_stats.max_ns.toFloat
    let ioMedian := formatNanos timings.io_stats.median_ns

    IO.println s!"  [{timings.backend_name}] Translation: {translateMedian} (range: {translateMin}-{translateMax}) | I/O: {ioMedian} | Size: {timings.file_size_bytes}b"
    IO.println s!"    → {workflowBaseDir}/{getBackendDirName backend}/{basename}.{ext}"

    writeHeader := false

-- ============================================================================
-- N-Queens CSP Definition
-- ============================================================================

-- Helper to create bound constraints for N-Queens
def queens_bounds (n : ℕ) : List (IntConstraint n) :=
  (List.finRange n).map fun i => bound i 1 n

-- General N-Queens CSP - parametrized for any board size
def nqueens_csp (n : ℕ) : IntCSP :=
  ⟨n, queens_bounds n ++ [
    alldifferent (_root_.Vector.ofFn id),
    alldifferent_diag_pos n,
    alldifferent_diag_neg n
  ]⟩

-- Generate instance for a specific size
def generate_instance (n : ℕ) (isFirst : Bool) : IO Unit := do
  let csp := nqueens_csp n
  let basename := s!"nqueens_{n}"
  saveAllBackendsTimedMultiRun basename csp isFirst

-- ============================================================================
-- Main Entry Point
-- ============================================================================

def main : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════════╗"
  IO.println "║  N-Queens Workflow Demonstration: Instance Generation             ║"
  IO.println "║  Generating instances for sizes 10-150 (step 10)                 ║"
  IO.println s!"║  Benchmarking: {WARMUP_RUNS} warmup + {MEASURED_RUNS} measured runs per translation     ║"
  IO.println "╚═══════════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Clear/create CSV file
  IO.FS.writeFile workflowTimingCSVPath ""

  -- Sizes: 10, 20, 30, ..., 150 (15 instances)
  let sizes := [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150]

  let mut idx := 0
  for n in sizes do
    idx := idx + 1
    IO.println s!"[{idx}/15] Generating N-Queens(n={n})..."
    generate_instance n (idx == 1)

  IO.println ""
  IO.println "✓ Generation complete!"
  IO.println s!"  - Generated 15 instances × 2 backends = 30 files"
  IO.println s!"  - MiniZinc: {workflowBaseDir}/mzn/nqueens_*.mzn"
  IO.println s!"  - SMT-LIB:  {workflowBaseDir}/smt2/nqueens_*.smt2"
  IO.println s!"  - Timing data: {workflowTimingCSVPath}"
  IO.println s!"  - Statistics: mean, median, min, max from {MEASURED_RUNS} runs (after {WARMUP_RUNS} warmup)"
