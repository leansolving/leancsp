#!/usr/bin/env python3
"""
Solver Benchmark Runner for L2S Test Instances
Runs Chuffed, Gecode, Z3, and CVC5 on all 32 translated test instances
"""

import subprocess
import time
import csv
import json
import re
import shutil
from pathlib import Path
from typing import Dict, List, Optional
from dataclasses import dataclass, asdict

# Paths
PROJECT_ROOT = Path("/home/pablo/projects/lean-csp/projects/CSP")
TEST_DIR = PROJECT_ROOT / "CSP/L2S/Tests"
MZN_DIR = TEST_DIR / "mzn"
SMT_DIR = TEST_DIR / "smt2"
RESULTS_FILE = TEST_DIR / "solver_benchmark_results.csv"

# Configuration
TIMEOUT = 60  # seconds

@dataclass
class SolverResult:
    """Solver result with timing and statistics."""
    problem_name: str
    solver: str
    backend: str  # "MiniZinc" or "SMT-LIB"
    status: str  # SAT, UNSAT, TIMEOUT, ERROR
    solve_time_s: Optional[float] = None  # Solver-reported time
    wall_time_s: Optional[float] = None  # Python-measured time
    failures: Optional[int] = None
    propagations: Optional[int] = None
    conflicts: Optional[int] = None
    decisions: Optional[int] = None
    nodes: Optional[int] = None
    memory_mb: Optional[float] = None
    timeout: bool = False
    error: str = ""

    def to_dict(self):
        """Convert to dict for CSV, replacing None with empty string."""
        d = asdict(self)
        return {k: ('' if v is None else v) for k, v in d.items()}


def check_solver_available(solver: str) -> bool:
    """Check if a solver is available in PATH."""
    return shutil.which(solver) is not None


def discover_instances() -> List[tuple[str, Path, Optional[Path]]]:
    """
    Discover all test instances (flat file structure).
    Returns: List of (problem_name, mzn_path, smt_path)
    """
    instances = []

    # Scan MiniZinc directory
    mzn_files = sorted(MZN_DIR.glob("*.mzn"))

    for mzn_file in mzn_files:
        problem_name = mzn_file.stem  # e.g., "08_queens"

        # Find corresponding SMT file
        smt_file = SMT_DIR / f"{problem_name}.smt2"
        smt_path = smt_file if smt_file.exists() else None

        instances.append((problem_name, mzn_file, smt_path))

    return instances


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

                # Extract timing
                if 'solveTime' in stat_data:
                    stats['solve_time'] = stat_data['solveTime']
                elif 'time' in stat_data:
                    stats['solve_time'] = stat_data['time']

                # Extract search stats
                if 'failures' in stat_data:
                    stats['failures'] = stat_data['failures']
                if 'propagations' in stat_data:
                    stats['propagations'] = stat_data['propagations']
                if 'nodes' in stat_data:
                    stats['nodes'] = stat_data['nodes']
                if 'peakMemory' in stat_data:
                    stats['memory_mb'] = stat_data['peakMemory']

        except json.JSONDecodeError:
            continue

    return stats


def parse_z3_sexpr_stats(output: str) -> Dict:
    """Parse Z3 -st S-expression statistics."""
    stats = {}

    # Find statistics S-expression
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
        elif key_normalized in ('memory', 'max_memory'):
            stats['memory_mb'] = float(value)

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
            # Parse time with units: "2ms", "1.5s"
            time_match = re.match(r'([\d.]+)(ms|s)', value)
            if time_match:
                time_val, unit = time_match.groups()
                time_seconds = float(time_val) / 1000 if unit == 'ms' else float(time_val)
                stats['solve_time'] = time_seconds

        elif 'conflicts' in key:
            conflict_match = re.match(r'(\d+)', value)
            if conflict_match:
                stats['conflicts'] = int(conflict_match.group(1))

        elif 'propagations' in key:
            prop_match = re.match(r'(\d+)', value)
            if prop_match:
                stats['propagations'] = int(prop_match.group(1))

    return stats


def run_minizinc(problem_name: str, mzn_file: Path, solver: str) -> SolverResult:
    """Run MiniZinc with specified solver (Chuffed or Gecode)."""
    result = SolverResult(
        problem_name=problem_name,
        solver=solver,
        backend="MiniZinc",
        status='UNKNOWN'
    )

    try:
        start = time.time()
        proc = subprocess.run(
            ['minizinc', '--solver', solver,
             '--time-limit', str(TIMEOUT * 1000),  # Milliseconds
             '--statistics', '--solver-statistics', '--json-stream',
             str(mzn_file)],
            capture_output=True,
            text=True,
            timeout=TIMEOUT + 5  # Extra margin for Python timeout
        )
        result.wall_time_s = time.time() - start

        # Parse statistics
        parsed_stats = parse_minizinc_json_stats(proc.stdout)
        result.solve_time_s = parsed_stats.get('solve_time')
        result.failures = parsed_stats.get('failures')
        result.propagations = parsed_stats.get('propagations')
        result.nodes = parsed_stats.get('nodes')
        result.memory_mb = parsed_stats.get('memory_mb')

        # Determine status
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

        if result.status == 'UNKNOWN' and proc.returncode != 0:
            result.status = 'ERROR'
            result.error = f"Exit code {proc.returncode}"

    except subprocess.TimeoutExpired:
        result.status = 'TIMEOUT'
        result.timeout = True
        result.wall_time_s = TIMEOUT
    except FileNotFoundError:
        result.status = 'ERROR'
        result.error = "Solver not found"
    except Exception as e:
        result.status = 'ERROR'
        result.error = str(e)

    return result


def run_smt(problem_name: str, smt_file: Path, solver: str) -> SolverResult:
    """Run SMT solver (Z3 or CVC5)."""
    result = SolverResult(
        problem_name=problem_name,
        solver=solver,
        backend="SMT-LIB",
        status='UNKNOWN'
    )

    try:
        start = time.time()

        # Build command with timeout flag
        if solver == 'z3':
            cmd = ['z3', f'-T:{TIMEOUT}', '-st', str(smt_file)]
        elif solver == 'cvc5':
            cmd = ['cvc5', f'--tlimit={TIMEOUT * 1000}', '--stats', str(smt_file)]
        else:
            result.status = 'ERROR'
            result.error = f"Unknown solver: {solver}"
            return result

        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=TIMEOUT + 5
        )
        result.wall_time_s = time.time() - start

        # Parse statistics (Z3: stdout, CVC5: stderr)
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
        result.memory_mb = parsed_stats.get('memory_mb')

        # Determine status - check first line only to avoid matching statistics
        first_line = proc.stdout.split('\n')[0].strip().lower() if proc.stdout else ''

        if first_line == 'unsat':
            result.status = 'UNSAT'
        elif first_line == 'sat':
            result.status = 'SAT'
        elif first_line == 'unknown':
            result.status = 'UNKNOWN'
        elif proc.returncode != 0:
            result.status = 'ERROR'
            result.error = f"Exit code {proc.returncode}"
        else:
            result.status = 'UNKNOWN'

    except subprocess.TimeoutExpired:
        result.status = 'TIMEOUT'
        result.timeout = True
        result.wall_time_s = TIMEOUT
    except FileNotFoundError:
        result.status = 'ERROR'
        result.error = "Solver not found"
    except Exception as e:
        result.status = 'ERROR'
        result.error = str(e)

    return result


def run_all_benchmarks() -> List[SolverResult]:
    """Run all benchmarks and collect results."""

    # Check solver availability
    print("Checking solver availability...")
    available_mzn_solvers = []
    available_smt_solvers = []

    if check_solver_available('minizinc'):
        for solver in ['Chuffed', 'Gecode']:
            available_mzn_solvers.append(solver)
            print(f"  ✓ MiniZinc solver: {solver}")

    for solver in ['z3', 'cvc5']:
        if check_solver_available(solver):
            available_smt_solvers.append(solver)
            print(f"  ✓ SMT solver: {solver}")

    if not available_mzn_solvers and not available_smt_solvers:
        print("ERROR: No solvers available!")
        return []

    # Discover instances
    print("\nDiscovering test instances...")
    instances = discover_instances()
    print(f"Found {len(instances)} instances\n")

    # Calculate total runs
    total_runs = 0
    for _, mzn_path, smt_path in instances:
        if mzn_path and mzn_path.exists():
            total_runs += len(available_mzn_solvers)
        if smt_path and smt_path.exists():
            total_runs += len(available_smt_solvers)

    print(f"Running {total_runs} benchmarks (timeout={TIMEOUT}s)...\n")

    # Run benchmarks
    results = []
    current = 0
    timeout_count = 0
    error_count = 0

    for problem_name, mzn_path, smt_path in instances:
        # MiniZinc solvers
        if mzn_path and mzn_path.exists():
            for solver in available_mzn_solvers:
                current += 1
                print(f"[{current:3d}/{total_runs}] [{solver:8s}] {problem_name:30s} ... ",
                      end='', flush=True)

                result = run_minizinc(problem_name, mzn_path, solver)
                results.append(result)

                # Display result
                status_symbol = {
                    'SAT': '✓',
                    'UNSAT': '✓',
                    'TIMEOUT': '⏱',
                    'ERROR': '✗',
                    'UNKNOWN': '?'
                }.get(result.status, '?')

                time_str = f"{result.wall_time_s:.2f}s" if result.wall_time_s else "N/A"
                print(f"{status_symbol} {result.status:8s} {time_str}")

                if result.timeout:
                    timeout_count += 1
                if result.status == 'ERROR':
                    error_count += 1

        # SMT solvers
        if smt_path and smt_path.exists():
            for solver in available_smt_solvers:
                current += 1
                print(f"[{current:3d}/{total_runs}] [{solver:8s}] {problem_name:30s} ... ",
                      end='', flush=True)

                result = run_smt(problem_name, smt_path, solver)
                results.append(result)

                # Display result
                status_symbol = {
                    'SAT': '✓',
                    'UNSAT': '✓',
                    'TIMEOUT': '⏱',
                    'ERROR': '✗',
                    'UNKNOWN': '?'
                }.get(result.status, '?')

                time_str = f"{result.wall_time_s:.2f}s" if result.wall_time_s else "N/A"
                print(f"{status_symbol} {result.status:8s} {time_str}")

                if result.timeout:
                    timeout_count += 1
                if result.status == 'ERROR':
                    error_count += 1

    print(f"\nCompleted: {current}/{total_runs} runs | Timeouts: {timeout_count} | Errors: {error_count}")
    return results


def write_results_csv(results: List[SolverResult], output_file: Path):
    """Write results to CSV."""
    with open(output_file, 'w', newline='') as f:
        fieldnames = [
            'problem_name', 'solver', 'backend', 'status',
            'solve_time_s', 'wall_time_s',
            'failures', 'propagations', 'conflicts', 'decisions', 'nodes',
            'memory_mb', 'timeout', 'error'
        ]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()

        for result in results:
            writer.writerow(result.to_dict())

    print(f"\n✓ Results written to: {output_file}")


def print_summary(results: List[SolverResult]):
    """Print summary statistics."""
    print("\n" + "=" * 80)
    print("SUMMARY")
    print("=" * 80)

    solvers = sorted(set(r.solver for r in results))

    for solver in solvers:
        solver_results = [r for r in results if r.solver == solver]
        sat_count = sum(1 for r in solver_results if r.status == 'SAT')
        unsat_count = sum(1 for r in solver_results if r.status == 'UNSAT')
        timeout_count = sum(1 for r in solver_results if r.timeout)
        error_count = sum(1 for r in solver_results if r.status == 'ERROR')

        solve_times = [r.solve_time_s for r in solver_results if r.solve_time_s is not None]
        avg_time = sum(solve_times) / len(solve_times) if solve_times else 0

        print(f"\n{solver} ({len(solver_results)} runs):")
        print(f"  SAT:      {sat_count}")
        print(f"  UNSAT:    {unsat_count}")
        print(f"  Timeout:  {timeout_count}")
        print(f"  Error:    {error_count}")
        print(f"  Avg time: {avg_time:.3f}s")


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Run solver benchmarks on L2S test instances')
    parser.add_argument('--timeout', type=int, default=60,
                       help='Timeout in seconds (default: 60)')
    args = parser.parse_args()

    global TIMEOUT
    TIMEOUT = args.timeout

    print("=" * 80)
    print("L2S Solver Benchmarks")
    print("=" * 80)
    print(f"Test directory: {TEST_DIR}")
    print(f"Timeout: {TIMEOUT}s")
    print()

    # Run benchmarks
    results = run_all_benchmarks()

    if not results:
        print("No results collected.")
        return

    # Write CSV
    write_results_csv(results, RESULTS_FILE)

    # Print summary
    print_summary(results)

    print("\n" + "=" * 80)
    print("DONE!")
    print("=" * 80)
    print(f"\nResults: {RESULTS_FILE}")
    print(f"Total runs: {len(results)}")
    print("\nTo analyze:")
    print(f"  column -t -s, {RESULTS_FILE} | less")
    print(f"  python3 -c \"import pandas as pd; df = pd.read_csv('{RESULTS_FILE}'); print(df.groupby('solver')['solve_time_s'].describe())\"")


if __name__ == '__main__':
    main()
