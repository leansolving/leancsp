#!/usr/bin/env python3
"""
Enhanced Symmetry Breaking Experiment Runner
Extracts detailed solver statistics from MiniZinc, Z3, and CVC5
"""

import subprocess
import time
import csv
import json
import re
import shutil
import statistics
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from dataclasses import dataclass, asdict
from collections import Counter

# Optional plotting
try:
    import matplotlib.pyplot as plt
    import numpy as np
    HAS_PLOTTING = True
except ImportError:
    HAS_PLOTTING = False
    print("matplotlib not available - plots will be skipped")

PROJECT_ROOT = Path("/home/pablo/projects/lean-csp/projects/CSP")
MZN_DIR = PROJECT_ROOT / "CSP/L2S/Proofs/mzn"
SMT_DIR = PROJECT_ROOT / "CSP/L2S/Proofs/smt2"
RESULTS_DIR = PROJECT_ROOT / "CSP/L2S/Proofs/Experiments/results"
PLOTS_DIR = PROJECT_ROOT / "CSP/L2S/Proofs/Experiments/plots"

# Default configuration
DEFAULT_TIMEOUT = 120      # 2 minutes (configurable via --timeout)
DEFAULT_NUM_RUNS = 5       # 5 measured runs per instance (configurable via --runs)
DISCARD_COLD_RUN = True    # Discard first "cold" run for warm-up

# Global timeout (will be set from command line)
TIMEOUT = DEFAULT_TIMEOUT

@dataclass
class SolverResult:
    """Detailed solver result with statistics."""
    problem: str
    size: int
    variant: str
    solver: str
    backend: str
    status: str  # SAT, UNSAT, TIMEOUT, ERROR, NOT_FOUND

    # Run tracking
    run_id: int = 0  # Which run (0, 1, 2, ...)

    # Timing
    wall_time: Optional[float] = None  # Manual timing
    solve_time: Optional[float] = None  # Solver-reported
    compilation_time: Optional[float] = None  # MiniZinc only

    # Search statistics
    conflicts: Optional[int] = None
    propagations: Optional[int] = None
    decisions: Optional[int] = None
    nodes: Optional[int] = None
    failures: Optional[int] = None

    # Resources
    memory_mb: Optional[float] = None

    def to_dict(self):
        """Convert to dict, replacing None with empty string for CSV."""
        d = asdict(self)
        return {k: ('' if v is None else v) for k, v in d.items()}


@dataclass
class AggregatedResult:
    """Aggregated statistics from multiple runs."""
    problem: str
    size: int
    variant: str
    solver: str
    backend: str
    status: str  # Majority status across runs

    # Aggregated timing
    time_median: Optional[float] = None
    time_mean: Optional[float] = None
    time_std: Optional[float] = None
    time_min: Optional[float] = None
    time_max: Optional[float] = None

    # PAR2 score (penalized average: timeout = 2 × TIMEOUT)
    par2: Optional[float] = None

    # Run counts
    num_runs: int = 0
    num_sat: int = 0
    num_unsat: int = 0
    num_timeout: int = 0
    num_error: int = 0

    def to_dict(self):
        """Convert to dict, replacing None with empty string for CSV."""
        d = asdict(self)
        return {k: ('' if v is None else v) for k, v in d.items()}


def check_solver_available(solver: str) -> bool:
    """Check if a solver is available in PATH."""
    return shutil.which(solver) is not None


def majority_status(results: List[SolverResult]) -> str:
    """Return the most common status from a list of results."""
    if not results:
        return 'UNKNOWN'
    status_counts = Counter(r.status for r in results)
    return status_counts.most_common(1)[0][0]


def aggregate_results(results: List[SolverResult], timeout: float) -> AggregatedResult:
    """Aggregate multiple runs into summary statistics."""
    if not results:
        return AggregatedResult(
            problem='', size=0, variant='', solver='', backend='',
            status='UNKNOWN'
        )

    # Get timing data (prefer solve_time, fall back to wall_time)
    times = []
    for r in results:
        t = r.solve_time if r.solve_time is not None else r.wall_time
        if t is not None and r.status not in ('TIMEOUT', 'ERROR', 'NOT_FOUND'):
            times.append(t)

    # Compute PAR2 (penalize timeouts as 2×timeout)
    par2_times = []
    for r in results:
        if r.status == 'TIMEOUT':
            par2_times.append(2 * timeout)
        else:
            t = r.solve_time if r.solve_time is not None else r.wall_time
            if t is not None:
                par2_times.append(t)

    # Compute statistics
    time_median = statistics.median(times) if times else None
    time_mean = statistics.mean(times) if times else None
    time_std = statistics.stdev(times) if len(times) > 1 else 0.0 if times else None
    time_min = min(times) if times else None
    time_max = max(times) if times else None
    par2 = statistics.mean(par2_times) if par2_times else None

    return AggregatedResult(
        problem=results[0].problem,
        size=results[0].size,
        variant=results[0].variant,
        solver=results[0].solver,
        backend=results[0].backend,
        status=majority_status(results),
        time_median=time_median,
        time_mean=time_mean,
        time_std=time_std,
        time_min=time_min,
        time_max=time_max,
        par2=par2,
        num_runs=len(results),
        num_sat=sum(1 for r in results if r.status == 'SAT'),
        num_unsat=sum(1 for r in results if r.status == 'UNSAT'),
        num_timeout=sum(1 for r in results if r.status == 'TIMEOUT'),
        num_error=sum(1 for r in results if r.status in ('ERROR', 'NOT_FOUND')),
    )


def discover_instances() -> List[Tuple[str, int, str, Path, Optional[Path]]]:
    """
    Auto-discover test instances by scanning directories.
    Returns: List of (problem_type, size, variant, mzn_path, smt_path)
    """
    instances = []

    # Scan MiniZinc directory for all .mzn files
    for mzn_file in MZN_DIR.rglob("*.mzn"):
        # Skip if in a hidden directory
        if any(part.startswith('.') for part in mzn_file.parts):
            continue

        # Extract problem type from directory structure
        # e.g., mzn/nqueens/base_10.mzn → problem=nqueens
        #       mzn/graphcoloring/random/base_250_critical.mzn → problem=graphcoloring_random
        rel_path = mzn_file.relative_to(MZN_DIR)
        problem_parts = list(rel_path.parent.parts)
        problem = '_'.join(problem_parts) if problem_parts else 'unknown'

        # Parse filename to extract size and variant
        # Patterns: base_10.mzn, sbc_20.mzn, base_250_hard_unsat.mzn
        stem = mzn_file.stem

        # Try to extract variant and size
        if stem.startswith('base_'):
            variant = 'base'
            size_str = stem[5:]  # Remove 'base_'
        elif stem.startswith('sbc_'):
            variant = 'sbc'
            size_str = stem[4:]  # Remove 'sbc_'
        else:
            continue  # Skip non-matching files

        # Extract numeric size (may have suffix like _hard_unsat)
        match = re.match(r'(\d+)', size_str)
        if not match:
            continue
        size = int(match.group(1))

        # Check for corresponding SMT file
        smt_file = SMT_DIR / rel_path.with_suffix('.smt2')
        smt_path = smt_file if smt_file.exists() else None

        instances.append((problem, size, variant, mzn_file, smt_path))

    # Sort by problem, size, variant
    instances.sort(key=lambda x: (x[0], x[1], x[2]))

    return instances


def parse_minizinc_json_stats(output: str) -> Dict:
    """Parse MiniZinc --json-stream output for statistics."""
    stats = {}

    # MiniZinc outputs multiple statistics JSON objects - merge them all
    for line in output.splitlines():
        line = line.strip()
        if not line or not line.startswith('{'):
            continue

        try:
            obj = json.loads(line)
            if obj.get('type') == 'statistics':
                stat_data = obj.get('statistics', {})

                # Extract timing (update if present)
                if 'solveTime' in stat_data:
                    stats['solve_time'] = stat_data['solveTime']
                elif 'time' in stat_data:
                    stats['solve_time'] = stat_data['time']

                if 'flatTime' in stat_data:
                    stats['compilation_time'] = stat_data['flatTime']

                # Extract search stats (update if present)
                if 'failures' in stat_data:
                    stats['failures'] = stat_data['failures']
                if 'propagations' in stat_data:
                    stats['propagations'] = stat_data['propagations']
                if 'nodes' in stat_data:
                    stats['nodes'] = stat_data['nodes']
                if 'peakMemory' in stat_data:
                    stats['memory_mb'] = stat_data['peakMemory']

                # Continue to next line (don't break - merge all statistics)
        except json.JSONDecodeError:
            continue

    return stats


def parse_z3_sexpr_stats(output: str) -> Dict:
    """Parse Z3 -st S-expression statistics."""
    stats = {}

    # Find the statistics S-expression (can span multiple lines)
    # Example:
    # (:max-memory   17.20
    #  :memory       17.20
    #  :total-time   0.01)
    stat_match = re.search(r'\((:[\w-]+\s+[\d.]+\s*)+\)', output, re.MULTILINE | re.DOTALL)
    if not stat_match:
        return stats

    stat_str = stat_match.group(0)

    # Parse key-value pairs (handle both _ and - in keys)
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
    """Parse CVC5 --stats key=value output."""
    stats = {}

    for line in output.splitlines():
        line = line.strip()

        # Parse key = value lines
        match = re.match(r'([\w:]+)\s*=\s*(.+)', line)
        if not match:
            continue

        key, value = match.groups()

        # Extract relevant statistics
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


def run_minizinc(mzn_file: Path, solver: str) -> SolverResult:
    """Run MiniZinc with statistics extraction."""
    result = SolverResult(
        problem='', size=0, variant='', solver=solver, backend='minizinc',
        status='UNKNOWN'
    )

    try:
        start = time.time()
        proc = subprocess.run(
            ['minizinc', '--solver', solver, '--statistics',
             '--solver-statistics', '--json-stream', str(mzn_file)],
            capture_output=True,
            text=True,
            timeout=TIMEOUT
        )
        result.wall_time = time.time() - start

        # Parse JSON statistics
        parsed_stats = parse_minizinc_json_stats(proc.stdout)
        result.solve_time = parsed_stats.get('solve_time')
        result.compilation_time = parsed_stats.get('compilation_time')
        result.failures = parsed_stats.get('failures')
        result.propagations = parsed_stats.get('propagations')
        result.nodes = parsed_stats.get('nodes')
        result.memory_mb = parsed_stats.get('memory_mb')

        # Determine status from JSON stream
        # For SAT: {"type": "solution", ...}
        # For UNSAT: {"type": "status", "status": "UNSATISFIABLE"}
        # For optimization: {"type": "status", "status": "OPTIMAL_SOLUTION"}
        result.status = 'UNKNOWN'
        has_solution = False

        for line in proc.stdout.splitlines():
            line = line.strip()
            if not line or not line.startswith('{'):
                continue
            try:
                obj = json.loads(line)
                obj_type = obj.get('type', '')

                # Check for solution (indicates SAT)
                if obj_type == 'solution':
                    has_solution = True

                # Check for status line
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

        # If we found a solution but no explicit status, it's SAT
        if result.status == 'UNKNOWN' and has_solution:
            result.status = 'SAT'

        # Fallback to return code if status not found in JSON
        if result.status == 'UNKNOWN' and proc.returncode != 0:
            result.status = 'ERROR'

    except subprocess.TimeoutExpired:
        result.status = 'TIMEOUT'
    except FileNotFoundError:
        result.status = 'NOT_FOUND'
    except Exception:
        result.status = 'ERROR'

    return result


def run_smt(smt_file: Path, solver: str) -> SolverResult:
    """Run SMT solver (Z3 or CVC5) with statistics extraction."""
    result = SolverResult(
        problem='', size=0, variant='', solver=solver, backend='smt',
        status='UNKNOWN'
    )

    try:
        start = time.time()

        # Build command with statistics flags
        if solver == 'z3':
            cmd = ['z3', '-st', str(smt_file)]
        elif solver == 'cvc5':
            cmd = ['cvc5', '--stats', str(smt_file)]
        else:
            result.status = 'UNKNOWN_SOLVER'
            return result

        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=TIMEOUT + 5
        )
        result.wall_time = time.time() - start

        # Parse solver-specific statistics
        # Note: Z3 outputs to stdout, CVC5 to stderr
        if solver == 'z3':
            parsed_stats = parse_z3_sexpr_stats(proc.stdout)
        elif solver == 'cvc5':
            parsed_stats = parse_cvc5_stats(proc.stderr)  # CVC5 stats go to stderr!
        else:
            parsed_stats = {}

        result.solve_time = parsed_stats.get('solve_time')
        result.conflicts = parsed_stats.get('conflicts')
        result.propagations = parsed_stats.get('propagations')
        result.decisions = parsed_stats.get('decisions')
        result.memory_mb = parsed_stats.get('memory_mb')

        # Determine status
        output = (proc.stdout + proc.stderr).lower()
        if 'unsat' in output:
            result.status = 'UNSAT'
        elif 'sat' in output:
            result.status = 'SAT'
        elif proc.returncode != 0:
            result.status = 'ERROR'
        else:
            result.status = 'UNKNOWN'

    except subprocess.TimeoutExpired:
        result.status = 'TIMEOUT'
    except FileNotFoundError:
        result.status = 'NOT_FOUND'
    except Exception:
        result.status = 'ERROR'

    return result


def run_all_experiments(
    dry_run: bool = False,
    num_runs: int = DEFAULT_NUM_RUNS,
    discard_cold_run: bool = DISCARD_COLD_RUN,
    exclude_pattern: Optional[str] = None,
    include_pattern: Optional[str] = None
) -> Tuple[List[SolverResult], List[AggregatedResult]]:
    """Run all experiments with multiple runs and collect detailed results.

    Args:
        dry_run: If True, only show what would be tested
        num_runs: Number of measured runs per instance (default: 5)
        discard_cold_run: If True, run one extra time and discard first run (default: True)
        exclude_pattern: If set, exclude instances whose problem name contains this string
        include_pattern: If set, only include instances whose problem name contains this string

    Returns:
        Tuple of (all_individual_results, aggregated_results)
    """

    # Check solver availability
    available_mzn_solvers = []
    available_smt_solvers = []

    print("Checking solver availability...")
    for solver in ['gecode', 'chuffed']:
        if check_solver_available('minizinc'):
            available_mzn_solvers.append(solver)
            print(f"  ✓ MiniZinc solver: {solver}")

    for solver in ['z3', 'cvc5']:
        if check_solver_available(solver):
            available_smt_solvers.append(solver)
            print(f"  ✓ SMT solver: {solver}")

    if not available_mzn_solvers and not available_smt_solvers:
        print("ERROR: No solvers available!")
        return [], []

    # Discover instances
    print("\nDiscovering test instances...")
    instances = discover_instances()

    # Filter instances based on include/exclude patterns
    original_count = len(instances)
    if include_pattern:
        instances = [inst for inst in instances if include_pattern in inst[0]]
    if exclude_pattern:
        instances = [inst for inst in instances if exclude_pattern not in inst[0]]

    if include_pattern or exclude_pattern:
        filters = []
        if include_pattern:
            filters.append(f"include '{include_pattern}'")
        if exclude_pattern:
            filters.append(f"exclude '{exclude_pattern}'")
        print(f"Found {original_count} instances, filtered to {len(instances)} ({', '.join(filters)})")
    else:
        print(f"Found {len(instances)} instances")

    # Calculate total runs
    total_actual_runs = num_runs + (1 if discard_cold_run else 0)
    num_solvers = len(available_mzn_solvers) + len(available_smt_solvers)
    total_experiments = len(instances) * num_solvers * total_actual_runs

    if dry_run:
        print(f"\nDRY RUN - would test (runs={num_runs}, warmup={discard_cold_run}):")
        for problem, size, variant, mzn, smt in instances[:10]:  # Show first 10
            print(f"  {problem:30s} n={size:4d} {variant:10s} "
                  f"[mzn: {mzn.exists()}] [smt: {smt.exists() if smt else False}]")
        if len(instances) > 10:
            print(f"  ... and {len(instances) - 10} more")
        print(f"\nTotal: {len(instances)} instances × {num_solvers} solvers × {total_actual_runs} runs = {total_experiments} solver calls")
        return [], []

    # Run experiments
    all_results = []
    aggregated_results = []
    current = 0

    print(f"\nRunning experiments (timeout={TIMEOUT}s, runs={num_runs}, warmup={discard_cold_run})...")
    print(f"Total solver calls: {total_experiments}\n")

    for problem, size, variant, mzn_file, smt_file in instances:

        # MiniZinc solvers
        if mzn_file and mzn_file.exists():
            for solver in available_mzn_solvers:
                instance_name = f"{problem} n={size} {variant}"
                run_results = []

                for run_id in range(total_actual_runs):
                    current += 1
                    is_warmup = discard_cold_run and run_id == 0

                    # Show progress
                    run_label = "warmup" if is_warmup else f"run {run_id if not discard_cold_run else run_id}"
                    print(f"  [{current}/{total_experiments}] {instance_name:40s} / {solver:8s} ({run_label}) ... ",
                          end='', flush=True)

                    result = run_minizinc(mzn_file, solver)
                    result.problem = problem
                    result.size = size
                    result.variant = variant
                    result.run_id = run_id

                    # Display result
                    if result.wall_time is not None:
                        time_str = f"{result.wall_time:.2f}s"
                        print(f"{time_str} ({result.status})")
                    else:
                        print(result.status)

                    # Skip warmup run
                    if is_warmup:
                        continue

                    run_results.append(result)
                    all_results.append(result)

                # Aggregate results for this instance+solver combination
                if run_results:
                    agg = aggregate_results(run_results, TIMEOUT)
                    aggregated_results.append(agg)
                    median_str = f"{agg.time_median:.3f}s" if agg.time_median is not None else "N/A"
                    std_str = f"{agg.time_std:.3f}s" if agg.time_std is not None else "N/A"
                    print(f"    → Aggregated: median={median_str}, "
                          f"std={std_str}, status={agg.status}\n")

        # SMT solvers
        if smt_file and smt_file.exists():
            for solver in available_smt_solvers:
                instance_name = f"{problem} n={size} {variant}"
                run_results = []

                for run_id in range(total_actual_runs):
                    current += 1
                    is_warmup = discard_cold_run and run_id == 0

                    # Show progress
                    run_label = "warmup" if is_warmup else f"run {run_id if not discard_cold_run else run_id}"
                    print(f"  [{current}/{total_experiments}] {instance_name:40s} / {solver:8s} ({run_label}) ... ",
                          end='', flush=True)

                    result = run_smt(smt_file, solver)
                    result.problem = problem
                    result.size = size
                    result.variant = variant
                    result.run_id = run_id

                    # Display result
                    if result.wall_time is not None:
                        time_str = f"{result.wall_time:.2f}s"
                        print(f"{time_str} ({result.status})")
                    else:
                        print(result.status)

                    # Skip warmup run
                    if is_warmup:
                        continue

                    run_results.append(result)
                    all_results.append(result)

                # Aggregate results for this instance+solver combination
                if run_results:
                    agg = aggregate_results(run_results, TIMEOUT)
                    aggregated_results.append(agg)
                    median_str = f"{agg.time_median:.3f}s" if agg.time_median is not None else "N/A"
                    std_str = f"{agg.time_std:.3f}s" if agg.time_std is not None else "N/A"
                    print(f"    → Aggregated: median={median_str}, "
                          f"std={std_str}, status={agg.status}\n")

    return all_results, aggregated_results


def write_detailed_csv(results: List[SolverResult], output_file: Path):
    """Write detailed results with all statistics to CSV (includes run_id)."""
    with open(output_file, 'w', newline='') as f:
        fieldnames = [
            'problem', 'size', 'variant', 'solver', 'backend', 'status', 'run_id',
            'wall_time', 'solve_time', 'compilation_time',
            'conflicts', 'propagations', 'decisions', 'nodes', 'failures',
            'memory_mb'
        ]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()

        for result in results:
            writer.writerow(result.to_dict())

    print(f"✓ Detailed CSV: {output_file}")


def write_aggregated_csv(results: List[AggregatedResult], output_file: Path):
    """Write aggregated results with statistics to CSV."""
    with open(output_file, 'w', newline='') as f:
        fieldnames = [
            'problem', 'size', 'variant', 'solver', 'backend', 'status',
            'time_median', 'time_mean', 'time_std', 'time_min', 'time_max',
            'par2', 'num_runs', 'num_sat', 'num_unsat', 'num_timeout', 'num_error'
        ]
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()

        for result in results:
            writer.writerow(result.to_dict())

    print(f"✓ Aggregated CSV: {output_file}")


def write_summary(results: List[SolverResult], output_file: Path):
    """Write human-readable summary."""
    with open(output_file, 'w') as f:
        f.write("Symmetry Breaking Experimental Results\n")
        f.write("=" * 80 + "\n\n")

        # Group by problem type
        problems = sorted(set(r.problem for r in results))

        for problem in problems:
            f.write(f"\n{problem.upper()}\n")
            f.write("-" * 80 + "\n")

            prob_results = [r for r in results if r.problem == problem]
            if not prob_results:
                f.write("No results\n")
                continue

            solvers = sorted(set(r.solver for r in prob_results))
            sizes = sorted(set(r.size for r in prob_results))

            for solver in solvers:
                f.write(f"\n{solver}:\n")
                f.write(f"{'Size':<8} {'BASE Time':<15} {'BASE Status':<12} "
                       f"{'+SBC Time':<15} {'+SBC Status':<12} {'Speedup':<10}\n")
                f.write("-" * 80 + "\n")

                for size in sizes:
                    base = next((r for r in prob_results
                                if r.size == size and r.variant == 'base' and r.solver == solver), None)
                    sbc = next((r for r in prob_results
                               if r.size == size and r.variant == 'sbc' and r.solver == solver), None)

                    if base and sbc:
                        # Use solver-reported time if available, else wall time
                        base_time = base.solve_time or base.wall_time
                        sbc_time = sbc.solve_time or sbc.wall_time

                        base_str = f"{base_time:.3f}s" if base_time else "TIMEOUT"
                        sbc_str = f"{sbc_time:.3f}s" if sbc_time else "TIMEOUT"

                        if base_time and sbc_time and sbc_time > 0:
                            speedup = base_time / sbc_time
                            speedup_str = f"{speedup:.2f}×"
                        else:
                            speedup_str = "-"

                        f.write(f"{size:<8} {base_str:<15} {base.status:<12} "
                               f"{sbc_str:<15} {sbc.status:<12} {speedup_str:<10}\n")

                f.write("\n")

    print(f"✓ Summary: {output_file}")


def main():
    global TIMEOUT

    import argparse

    parser = argparse.ArgumentParser(description='Run symmetry breaking experiments with multiple runs')
    parser.add_argument('--dry-run', action='store_true',
                       help='Show what would be tested without running')
    parser.add_argument('--runs', type=int, default=DEFAULT_NUM_RUNS,
                       help=f'Number of runs per instance (default: {DEFAULT_NUM_RUNS})')
    parser.add_argument('--no-warmup', action='store_true',
                       help='Do not discard first cold run')
    parser.add_argument('--timeout', type=int, default=DEFAULT_TIMEOUT,
                       help=f'Timeout in seconds per run (default: {DEFAULT_TIMEOUT})')
    parser.add_argument('--exclude', type=str, default=None,
                       help='Exclude instances matching this pattern (e.g., "random")')
    parser.add_argument('--include', type=str, default=None,
                       help='Only include instances matching this pattern (e.g., "graphcoloring")')
    args = parser.parse_args()

    # Set global timeout
    TIMEOUT = args.timeout

    print("=" * 80)
    print("Symmetry Breaking Experiments - Multiple Runs with Statistics")
    print("=" * 80)
    print(f"  Runs per instance: {args.runs}")
    print(f"  Warmup (discard cold run): {not args.no_warmup}")
    print(f"  Timeout per run: {TIMEOUT}s")
    print("=" * 80)

    # Create output directories
    RESULTS_DIR.mkdir(parents=True, exist_ok=True)

    # Run experiments
    detailed_results, aggregated_results = run_all_experiments(
        dry_run=args.dry_run,
        num_runs=args.runs,
        discard_cold_run=not args.no_warmup,
        exclude_pattern=args.exclude,
        include_pattern=args.include
    )

    if not detailed_results and not aggregated_results:
        return

    # Generate outputs
    print("\n" + "=" * 80)
    print("Generating outputs...")
    print("=" * 80)

    write_detailed_csv(detailed_results, RESULTS_DIR / "detailed_results.csv")
    write_aggregated_csv(aggregated_results, RESULTS_DIR / "aggregated_results.csv")
    write_summary(detailed_results, RESULTS_DIR / "summary.txt")

    print("\n" + "=" * 80)
    print("DONE!")
    print("=" * 80)
    print(f"\nResults: {RESULTS_DIR}")
    print(f"  - detailed_results.csv (all individual runs with run_id)")
    print(f"  - aggregated_results.csv (median, mean, std, min, max, PAR2)")
    print(f"  - summary.txt (human-readable)")


if __name__ == '__main__':
    main()
