#!/usr/bin/env python3
"""
N-Queens Workflow Demonstration: Translation vs Solving Time

Demonstrates that CSP translation overhead is negligible compared to solving time.

Workflow:
1. Generate N-Queens instances (n=10,20,...,150) using Lean
2. Parse translation times from timing data
3. Run 4 solvers (Chuffed, Gecode, Z3, CVC5) with 60s timeout
4. Combine results and calculate translation/solving ratio
5. Generate summary statistics

Output:
- results/translation_times.csv
- results/solver_times.csv
- results/combined_analysis.csv
"""

import subprocess
import time
import csv
import json
import re
import shutil
import statistics
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass, asdict
from collections import Counter

# Paths
PROJECT_ROOT = Path("/home/pablo/projects/lean-csp/projects/CSP")
WORKFLOW_DIR = PROJECT_ROOT / "CSP/L2S/Tests/workflow_demonstration"
RESULTS_DIR = WORKFLOW_DIR / "results"
# Lean generator writes to workflow_demonstration/{mzn,smt2}/ using custom save functions
MZN_DIR = WORKFLOW_DIR / "mzn"
SMT_DIR = WORKFLOW_DIR / "smt2"
# Lean generator writes timing data here (with statistics)
TIMING_CSV = WORKFLOW_DIR / "timing_results.csv"

# Configuration
SIZES = [10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120, 130, 140, 150]
#SIZES = [10, 20]
TIMEOUT = 60  # seconds

# Multi-run benchmarking configuration
WARMUP_RUNS = 1   # Discard first run(s) to avoid JIT/cache effects
MEASURED_RUNS = 5 # Number of measured runs for statistics

@dataclass
class TranslationData:
    """Translation timing data with statistics."""
    size: int
    backend: str
    # Translation statistics (in nanoseconds)
    translation_median_ns: float
    translation_min_ns: int
    translation_max_ns: int
    # File I/O statistics (in nanoseconds)
    io_median_ns: float
    io_min_ns: int
    io_max_ns: int
    file_size_bytes: int

@dataclass
class SolverResult:
    """Solver benchmark result from a single run."""
    size: int
    solver: str
    backend: str
    status: str  # SAT, UNSAT, TIMEOUT, ERROR
    wall_time_s: float
    solve_time_s: Optional[float] = None
    conflicts: Optional[int] = None
    propagations: Optional[int] = None
    decisions: Optional[int] = None

@dataclass
class SolverResultStats:
    """Solver benchmark result with statistics from multiple runs."""
    size: int
    solver: str
    backend: str
    warmup_runs: int
    measured_runs: int
    status: str  # SAT, UNSAT, TIMEOUT, ERROR (majority vote)
    # Wall time statistics
    wall_time_mean_s: float
    wall_time_median_s: float
    wall_time_min_s: float
    wall_time_max_s: float
    wall_time_std_s: float
    # Optional solver-reported stats (from last successful run)
    solve_time_s: Optional[float] = None
    conflicts: Optional[int] = None
    propagations: Optional[int] = None
    decisions: Optional[int] = None

@dataclass
class CombinedResult:
    """Combined analysis result."""
    size: int
    solver: str
    backend: str
    translation_ms: float
    solving_s: float
    total_s: float
    translation_pct: float
    status: str

def check_solver_available(solver: str) -> bool:
    """Check if a solver is available in PATH."""
    return shutil.which(solver) is not None

def parse_minizinc_json_stats(output: str) -> Dict:
    """Parse MiniZinc --json-stream output for statistics."""
    stats = {}
    for line in output.splitlines():
        line = line.strip()
        if not line or not line.startswith('{'):
            continue
        try:
            obj = json.loads(line)
            if obj.get('type') == 'statistics':
                stat_data = obj.get('statistics', {})
                if 'solveTime' in stat_data:
                    stats['solve_time'] = stat_data['solveTime']
                elif 'time' in stat_data:
                    stats['solve_time'] = stat_data['time']
                if 'failures' in stat_data:
                    stats['failures'] = stat_data['failures']
                if 'propagations' in stat_data:
                    stats['propagations'] = stat_data['propagations']
        except json.JSONDecodeError:
            continue
    return stats

def parse_z3_sexpr_stats(output: str) -> Dict:
    """Parse Z3 -st S-expression statistics."""
    stats = {}
    stat_match = re.search(r'\((:[\w-]+\s+[\d.]+\s*)+\)', output, re.MULTILINE | re.DOTALL)
    if not stat_match:
        return stats
    stat_str = stat_match.group(0)
    pairs = re.findall(r':([\w-]+)\s+([\d.]+)', stat_str)
    for key, value in pairs:
        key_normalized = key.replace('-', '_')
        if key_normalized in ('time', 'total_time'):
            stats['solve_time'] = float(value)
        elif key_normalized == 'conflicts':
            stats['conflicts'] = int(float(value))
        elif key_normalized == 'decisions':
            stats['decisions'] = int(float(value))
        elif key_normalized == 'propagations':
            stats['propagations'] = int(float(value))
    return stats

def parse_cvc5_stats(output: str) -> Dict:
    """Parse CVC5 --stats key=value output from stderr."""
    stats = {}
    for line in output.splitlines():
        line = line.strip()
        match = re.match(r'([\w:]+)\s*=\s*(.+)', line)
        if not match:
            continue
        key, value = match.groups()
        if 'totalTime' in key:
            time_match = re.match(r'([\d.]+)(ms|s)', value)
            if time_match:
                time_val, unit = time_match.groups()
                time_seconds = float(time_val) / 1000 if unit == 'ms' else float(time_val)
                stats['solve_time'] = time_seconds
    return stats

def run_minizinc(size: int, mzn_file: Path, solver: str) -> SolverResult:
    """Run MiniZinc with specified solver."""
    result = SolverResult(size=size, solver=solver, backend="MiniZinc",
                         status='UNKNOWN', wall_time_s=0.0)
    try:
        start = time.time()
        proc = subprocess.run(
            ['minizinc', '--solver', solver,
             '--time-limit', str(TIMEOUT * 1000),
             '--statistics', '--solver-statistics', '--json-stream',
             str(mzn_file)],
            capture_output=True,
            text=True,
            timeout=TIMEOUT + 5
        )
        result.wall_time_s = time.time() - start

        parsed_stats = parse_minizinc_json_stats(proc.stdout)
        result.solve_time_s = parsed_stats.get('solve_time')
        result.propagations = parsed_stats.get('propagations')

        result.status = 'UNKNOWN'
        has_solution = False
        for line in proc.stdout.splitlines():
            line = line.strip()
            if not line or not line.startswith('{'):
                continue
            try:
                obj = json.loads(line)
                obj_type = obj.get('type', '')
                if obj_type == 'solution':
                    has_solution = True
                elif obj_type == 'status':
                    status_value = obj.get('status', '').upper()
                    if 'SATISFIED' in status_value or 'OPTIMAL' in status_value:
                        result.status = 'SAT'
                        break
                    elif 'UNSATISFIABLE' in status_value or 'UNSAT' in status_value:
                        result.status = 'UNSAT'
                        break
            except json.JSONDecodeError:
                continue

        if result.status == 'UNKNOWN' and has_solution:
            result.status = 'SAT'
    except subprocess.TimeoutExpired:
        result.status = 'TIMEOUT'
        result.wall_time_s = TIMEOUT
    except Exception as e:
        result.status = 'ERROR'
        result.wall_time_s = 0.0
    return result

def run_smt(size: int, smt_file: Path, solver: str) -> SolverResult:
    """Run SMT solver."""
    result = SolverResult(size=size, solver=solver, backend="SMT-LIB",
                         status='UNKNOWN', wall_time_s=0.0)
    try:
        start = time.time()
        if solver == 'z3':
            cmd = ['z3', f'-T:{TIMEOUT}', '-st', str(smt_file)]
        elif solver == 'cvc5':
            cmd = ['cvc5', f'--tlimit={TIMEOUT * 1000}', '--stats', str(smt_file)]
        else:
            result.status = 'ERROR'
            return result

        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=TIMEOUT + 5)
        result.wall_time_s = time.time() - start

        if solver == 'z3':
            parsed_stats = parse_z3_sexpr_stats(proc.stdout)
        elif solver == 'cvc5':
            parsed_stats = parse_cvc5_stats(proc.stderr)
        else:
            parsed_stats = {}

        result.solve_time_s = parsed_stats.get('solve_time')
        result.conflicts = parsed_stats.get('conflicts')
        result.propagations = parsed_stats.get('propagations')
        result.decisions = parsed_stats.get('decisions')

        first_line = proc.stdout.split('\n')[0].strip().lower() if proc.stdout else ''
        if first_line == 'unsat':
            result.status = 'UNSAT'
        elif first_line == 'sat':
            result.status = 'SAT'
        elif first_line == 'unknown':
            result.status = 'UNKNOWN'
    except subprocess.TimeoutExpired:
        result.status = 'TIMEOUT'
        result.wall_time_s = TIMEOUT
    except Exception as e:
        result.status = 'ERROR'
        result.wall_time_s = 0.0
    return result

def compute_stats(timings: List[float], statuses: List[str],
                  last_result: SolverResult) -> SolverResultStats:
    """Compute statistics from multiple solver runs."""
    # Majority vote for status
    status_counts = Counter(statuses)
    majority_status = status_counts.most_common(1)[0][0]

    # Compute statistics
    mean_time = statistics.mean(timings)
    median_time = statistics.median(timings)
    min_time = min(timings)
    max_time = max(timings)
    std_time = statistics.stdev(timings) if len(timings) > 1 else 0.0

    return SolverResultStats(
        size=last_result.size,
        solver=last_result.solver,
        backend=last_result.backend,
        warmup_runs=WARMUP_RUNS,
        measured_runs=MEASURED_RUNS,
        status=majority_status,
        wall_time_mean_s=mean_time,
        wall_time_median_s=median_time,
        wall_time_min_s=min_time,
        wall_time_max_s=max_time,
        wall_time_std_s=std_time,
        solve_time_s=last_result.solve_time_s,
        conflicts=last_result.conflicts,
        propagations=last_result.propagations,
        decisions=last_result.decisions
    )

def run_minizinc_multi(size: int, mzn_file: Path, solver: str) -> SolverResultStats:
    """Run MiniZinc with specified solver multiple times and compute statistics."""
    # Warmup runs (discarded)
    for _ in range(WARMUP_RUNS):
        run_minizinc(size, mzn_file, solver)

    # Measured runs
    timings = []
    statuses = []
    last_result = None
    for _ in range(MEASURED_RUNS):
        result = run_minizinc(size, mzn_file, solver)
        timings.append(result.wall_time_s)
        statuses.append(result.status)
        last_result = result

    return compute_stats(timings, statuses, last_result)

def run_smt_multi(size: int, smt_file: Path, solver: str) -> SolverResultStats:
    """Run SMT solver multiple times and compute statistics."""
    # Warmup runs (discarded)
    for _ in range(WARMUP_RUNS):
        run_smt(size, smt_file, solver)

    # Measured runs
    timings = []
    statuses = []
    last_result = None
    for _ in range(MEASURED_RUNS):
        result = run_smt(size, smt_file, solver)
        timings.append(result.wall_time_s)
        statuses.append(result.status)
        last_result = result

    return compute_stats(timings, statuses, last_result)

def step1_generate_instances():
    """Step 1: Run Lean to generate all N-Queens instances."""
    print("\n" + "="*70)
    print("STEP 1: Generating N-Queens Instances")
    print("="*70)

    gen_file = WORKFLOW_DIR / "generate_instances.lean"
    print(f"Running: lake env lean --run {gen_file}")

    try:
        proc = subprocess.run(
            ['lake', 'env', 'lean', '--run', str(gen_file)],
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=600  # 10 minute timeout
        )
        print(proc.stdout)
        if proc.returncode != 0:
            print(f"ERROR: {proc.stderr}")
            return False
        return True
    except subprocess.TimeoutExpired:
        print("ERROR: Generation timed out after 10 minutes")
        return False
    except Exception as e:
        print(f"ERROR: {e}")
        return False

def step2_parse_translation_times() -> List[TranslationData]:
    """Step 2: Parse translation times from CSV (new format with statistics)."""
    print("\n" + "="*70)
    print("STEP 2: Parsing Translation Times")
    print("="*70)

    data = []
    with open(TIMING_CSV) as f:
        reader = csv.DictReader(f)
        for row in reader:
            if row['problem_name'].startswith('nqueens_'):
                size = int(row['problem_name'].split('_')[1])
                data.append(TranslationData(
                    size=size,
                    backend=row['backend'],
                    translation_median_ns=float(row['translate_median_ns']),
                    translation_min_ns=int(float(row['translate_min_ns'])),
                    translation_max_ns=int(float(row['translate_max_ns'])),
                    io_median_ns=float(row['io_median_ns']),
                    io_min_ns=int(float(row['io_min_ns'])),
                    io_max_ns=int(float(row['io_max_ns'])),
                    file_size_bytes=int(row['file_size_bytes'])
                ))

    print(f"Found translation data for {len(data)} instances")

    # Write to CSV with statistical columns
    csv_path = RESULTS_DIR / "translation_times.csv"
    with open(csv_path, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['size', 'backend', 'translation_median_ns', 'translation_min_ns',
                        'translation_max_ns', 'io_median_ns', 'io_min_ns', 'io_max_ns',
                        'file_size_bytes'])
        for d in data:
            writer.writerow([d.size, d.backend, d.translation_median_ns, d.translation_min_ns,
                           d.translation_max_ns, d.io_median_ns, d.io_min_ns, d.io_max_ns,
                           d.file_size_bytes])

    print(f"Saved: {csv_path}")
    return data

def step3_run_solvers() -> List[SolverResultStats]:
    """Step 3: Run solvers on generated instances with multi-run benchmarking."""
    print("\n" + "="*70)
    print("STEP 3: Running Solver Benchmarks")
    print(f"        ({WARMUP_RUNS} warmup + {MEASURED_RUNS} measured runs per solver)")
    print("="*70)

    # Check available solvers
    available_mzn = []
    available_smt = []
    if check_solver_available('minizinc'):
        for solver in ['Chuffed', 'Gecode']:
            available_mzn.append(solver)
            print(f"  ✓ MiniZinc solver: {solver}")
    for solver in ['z3', 'cvc5']:
        if check_solver_available(solver):
            available_smt.append(solver)
            print(f"  ✓ SMT solver: {solver}")

    if not available_mzn and not available_smt:
        print("ERROR: No solvers available!")
        return []

    results = []
    total_runs = len(SIZES) * (len(available_mzn) + len(available_smt))
    current = 0

    for size in SIZES:
        # MiniZinc solvers
        mzn_file = MZN_DIR / f"nqueens_{size}.mzn"
        if mzn_file.exists():
            for solver in available_mzn:
                current += 1
                print(f"[{current:3d}/{total_runs}] [{solver:8s}] nqueens_{size:3d} ... ",
                      end='', flush=True)
                result = run_minizinc_multi(size, mzn_file, solver)
                results.append(result)
                status_symbol = {'SAT': '✓', 'UNSAT': '✓', 'TIMEOUT': '⏱', 'ERROR': '✗'}
                print(f"{status_symbol.get(result.status, '?')} {result.status:8s} "
                      f"median={result.wall_time_median_s:.2f}s "
                      f"(range: {result.wall_time_min_s:.2f}-{result.wall_time_max_s:.2f}s)")

        # SMT solvers
        smt_file = SMT_DIR / f"nqueens_{size}.smt2"
        if smt_file.exists():
            for solver in available_smt:
                current += 1
                print(f"[{current:3d}/{total_runs}] [{solver:8s}] nqueens_{size:3d} ... ",
                      end='', flush=True)
                result = run_smt_multi(size, smt_file, solver)
                results.append(result)
                status_symbol = {'SAT': '✓', 'UNSAT': '✓', 'TIMEOUT': '⏱', 'ERROR': '✗'}
                print(f"{status_symbol.get(result.status, '?')} {result.status:8s} "
                      f"median={result.wall_time_median_s:.2f}s "
                      f"(range: {result.wall_time_min_s:.2f}-{result.wall_time_max_s:.2f}s)")

    # Write to CSV with statistics columns
    csv_path = RESULTS_DIR / "solver_times.csv"
    with open(csv_path, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['size', 'solver', 'backend', 'warmup_runs', 'measured_runs',
                        'status', 'wall_time_mean_s', 'wall_time_median_s',
                        'wall_time_min_s', 'wall_time_max_s', 'wall_time_std_s',
                        'solve_time_s', 'conflicts', 'propagations', 'decisions'])
        for r in results:
            writer.writerow([r.size, r.solver, r.backend, r.warmup_runs, r.measured_runs,
                           r.status, f"{r.wall_time_mean_s:.6f}", f"{r.wall_time_median_s:.6f}",
                           f"{r.wall_time_min_s:.6f}", f"{r.wall_time_max_s:.6f}",
                           f"{r.wall_time_std_s:.6f}",
                           r.solve_time_s or '', r.conflicts or '', r.propagations or '',
                           r.decisions or ''])

    print(f"\nSaved: {csv_path}")
    return results

def step4_combine_results(translation_data: List[TranslationData],
                         solver_results: List[SolverResultStats]) -> List[CombinedResult]:
    """Step 4: Combine translation and solving times (using median solve time)."""
    print("\n" + "="*70)
    print("STEP 4: Combining Results")
    print("="*70)

    # Create lookup dictionary for translation times
    trans_lookup = {}
    for t in translation_data:
        trans_lookup[(t.size, t.backend)] = t

    combined = []
    for s in solver_results:
        # Skip timeouts and errors for analysis
        if s.status in ['TIMEOUT', 'ERROR']:
            continue

        backend_key = "MiniZinc" if s.backend == "MiniZinc" else "SMT-LIB"
        trans = trans_lookup.get((s.size, backend_key))
        if not trans:
            continue

        translation_ms = trans.translation_median_ns / 1_000_000
        # Use median time for robust analysis
        solving_s = s.wall_time_median_s
        total_s = (trans.translation_median_ns / 1_000_000_000) + solving_s

        if solving_s > 0:
            translation_pct = (trans.translation_median_ns / 1_000_000_000) / solving_s * 100
        else:
            translation_pct = float('inf')

        combined.append(CombinedResult(
            size=s.size,
            solver=s.solver,
            backend=s.backend,
            translation_ms=translation_ms,
            solving_s=solving_s,
            total_s=total_s,
            translation_pct=translation_pct,
            status=s.status
        ))

    # Write to CSV
    csv_path = RESULTS_DIR / "combined_analysis.csv"
    with open(csv_path, 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(['size', 'solver', 'backend', 'translation_ms', 'solving_s',
                        'total_s', 'translation_pct', 'status'])
        for c in combined:
            writer.writerow([c.size, c.solver, c.backend, f"{c.translation_ms:.6f}",
                           f"{c.solving_s:.6f}", f"{c.total_s:.6f}",
                           f"{c.translation_pct:.4f}", c.status])

    print(f"Saved: {csv_path}")
    return combined

def step5_generate_summary(combined: List[CombinedResult]):
    """Step 5: Generate summary statistics (using median solve times)."""
    print("\n" + "="*70)
    print("STEP 5: Summary Statistics (using median solve times)")
    print("="*70)

    if not combined:
        print("No data to summarize")
        return

    # Calculate statistics
    translation_pcts = [c.translation_pct for c in combined if c.translation_pct < float('inf')]

    if translation_pcts:
        avg_pct = sum(translation_pcts) / len(translation_pcts)
        min_pct = min(translation_pcts)
        max_pct = max(translation_pcts)

        print(f"\nTranslation as % of solving time:")
        print(f"  Average: {avg_pct:.4f}%")
        print(f"  Minimum: {min_pct:.4f}%")
        print(f"  Maximum: {max_pct:.4f}%")

        # Count by threshold
        under_1pct = sum(1 for p in translation_pcts if p < 1.0)
        under_01pct = sum(1 for p in translation_pcts if p < 0.1)

        print(f"\nThreshold analysis:")
        print(f"  Translation < 1% of solving:  {under_1pct}/{len(translation_pcts)} runs ({under_1pct/len(translation_pcts)*100:.1f}%)")
        print(f"  Translation < 0.1% of solving: {under_01pct}/{len(translation_pcts)} runs ({under_01pct/len(translation_pcts)*100:.1f}%)")

    # Group by size
    print(f"\nResults by problem size:")
    for size in SIZES:
        size_results = [c for c in combined if c.size == size]
        if size_results:
            avg_trans = sum(c.translation_ms for c in size_results) / len(size_results)
            avg_solve = sum(c.solving_s for c in size_results) / len(size_results)
            print(f"  n={size:3d}: translation={avg_trans:7.3f}ms, solving={avg_solve:7.3f}s")

def main():
    print("\n" + "="*70)
    print("N-QUEENS WORKFLOW DEMONSTRATION")
    print("Translation vs Solving Time Comparison")
    print("="*70)
    print(f"Working directory: {WORKFLOW_DIR}")
    print(f"Timeout: {TIMEOUT}s per solver run")
    print(f"Benchmarking: {WARMUP_RUNS} warmup + {MEASURED_RUNS} measured runs")
    print(f"Sizes: {SIZES}")

    # Create results directory
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # Execute workflow
    if not step1_generate_instances():
        print("\nERROR: Failed to generate instances")
        return 1

    translation_data = step2_parse_translation_times()
    solver_results = step3_run_solvers()
    combined = step4_combine_results(translation_data, solver_results)
    step5_generate_summary(combined)

    print("\n" + "="*70)
    print("WORKFLOW COMPLETE!")
    print("="*70)
    print(f"Results directory: {RESULTS_DIR}")
    print(f"  - translation_times.csv")
    print(f"  - solver_times.csv")
    print(f"  - combined_analysis.csv")
    print("\nNext steps:")
    print(f"  python3 analyze_results.py  # Generate plots")

    return 0

if __name__ == '__main__':
    exit(main())
