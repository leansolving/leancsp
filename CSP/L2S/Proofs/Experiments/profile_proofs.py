#!/usr/bin/env python3
"""
Lean Proof Verification Performance Profiler
=============================================

This script profiles all Lean proof files in the L2S/Proofs directory,
measuring elaboration time, type checking time, and other performance metrics.

Usage:
    python3 profile_proofs.py

Output:
    - proof_metrics.csv: Detailed metrics for each proof file
    - proof_summary.txt: Human-readable summary

Author: Generated for CSP L2S Framework
Date: 2025-11-21
"""

import subprocess
import os
import re
import csv
from datetime import datetime
from typing import Dict, List, Tuple

# Configuration
PROJECT_ROOT = "/home/pablo/projects/lean-csp/projects/CSP"
PROOFS_DIR = "CSP/L2S/Proofs"
OUTPUT_CSV = "CSP/L2S/Proofs/Experiments/proof_metrics.csv"
OUTPUT_SUMMARY = "CSP/L2S/Proofs/Experiments/proof_summary.txt"
OUTPUT_LATEX = "CSP/L2S/Proofs/Experiments/proof_metrics.tex"

# Files to exclude from analysis
EXCLUDED_FILES = [
    "CircuitInputSymmetryBreaking.lean",  # Excluded per user request
    "NQueensEquivalence_temp.lean",       # Temporary file
    "ParityPathCSP.lean",
]

# Files to combine (child -> parent): child times will be added to parent
# UnreachableInputElimination is imported by ParityPathTheorem
COMBINE_FILES = {
    "UnreachableInputElimination.lean": "ParityPathTheorem.lean"
}

# Human-readable names for proof files
DISPLAY_NAMES = {
    "GraphColoringSB.lean": "Graph Coloring",
    "GraphColoringEquivalence.lean": "Graph Coloring Equivalence",
    "NQueensSB.lean": "N-Queens",
    "NQueensEquivalence.lean": "N-Queens Equivalence",
    "LatinSquareSB.lean": "Latin Square",
    "ParityPathTheorem.lean": "Parity Path Theorem",
    "UnreachableInputElimination.lean": "Unreachable Input Elimination",
}

def extract_metric(output: str, metric_name: str) -> Tuple[float, str]:
    """
    Extract a metric value from lean --profile output.

    Args:
        output: The full output from lean --profile
        metric_name: Name of the metric to extract (e.g., "elaboration")

    Returns:
        Tuple of (value in milliseconds, original string with unit)
    """
    pattern = rf'{metric_name}\s+(\d+\.?\d*)([a-zµ]+)'
    match = re.search(pattern, output)

    if not match:
        return 0.0, "N/A"

    value = float(match.group(1))
    unit = match.group(2)

    # Convert to milliseconds
    if unit == 's':
        value_ms = value * 1000
    elif unit == 'ms':
        value_ms = value
    elif unit == 'µs' or unit == 'us':
        value_ms = value / 1000
    else:
        value_ms = value  # Assume ms

    return value_ms, f"{match.group(1)}{unit}"

def count_lines(filepath: str) -> Tuple[int, int, int]:
    """
    Count lines in a file.

    Returns:
        Tuple of (total_lines, code_lines, comment_lines)
    """
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    total = len(lines)
    code = 0
    comments = 0

    for line in lines:
        stripped = line.strip()
        if not stripped:
            continue
        elif stripped.startswith('--'):
            comments += 1
        else:
            code += 1

    return total, code, comments

def profile_file(filepath: str) -> Dict[str, any]:
    """
    Profile a single Lean file and extract all metrics.

    Args:
        filepath: Path to the .lean file (relative to PROJECT_ROOT)

    Returns:
        Dictionary of metrics
    """
    print(f"Profiling: {os.path.basename(filepath)}...")

    # Run lean --profile
    result = subprocess.run(
        ['lake', 'env', 'lean', '--profile', filepath],
        capture_output=True,
        text=True,
        timeout=300,
        cwd=PROJECT_ROOT
    )

    output = result.stdout + result.stderr

    # Count lines
    full_path = os.path.join(PROJECT_ROOT, filepath)
    total_lines, code_lines, comment_lines = count_lines(full_path)

    # Extract all metrics
    metrics = {
        'file': os.path.basename(filepath),
        'total_lines': total_lines,
        'code_lines': code_lines,
        'comment_lines': comment_lines,
    }

    # Extract profiling times
    metric_names = [
        'elaboration',
        'type checking',
        'parsing',
        'import',
        'tactic execution',
        'simp',
        'interpretation',
        'initialization',
        'compilation (IR)',
        'compilation (LCNF base)',
        'compilation (LCNF mono)',
        'linting',
        'instantiate metavars',
    ]

    for metric in metric_names:
        value_ms, value_str = extract_metric(output, metric)
        # Replace spaces with underscores for column names
        col_name = metric.replace(' ', '_').replace('(', '').replace(')', '')
        metrics[f'{col_name}_ms'] = value_ms
        metrics[f'{col_name}_str'] = value_str

    # Calculate total verification time (elaboration + type checking)
    metrics['verification_time_ms'] = (
        metrics.get('elaboration_ms', 0) +
        metrics.get('type_checking_ms', 0)
    )

    # Calculate efficiency (code lines per millisecond of elaboration)
    if metrics.get('elaboration_ms', 0) > 0:
        metrics['efficiency'] = code_lines / metrics['elaboration_ms']
    else:
        metrics['efficiency'] = 0.0

    return metrics

def get_display_name(filename: str) -> str:
    """Get human-readable display name for a proof file."""
    if filename in DISPLAY_NAMES:
        return DISPLAY_NAMES[filename]
    # Fallback: remove .lean, replace underscores with spaces, title case
    name = filename.replace('.lean', '').replace('_', ' ')
    # Handle camelCase (re is already imported at module level)
    name = re.sub(r'([a-z])([A-Z])', r'\1 \2', name)
    return name


def combine_results(results: List[Dict[str, any]]) -> List[Dict[str, any]]:
    """
    Combine results for files that should be merged.

    For files in COMBINE_FILES, adds child file metrics to parent file
    and removes the child from results.
    """
    # Create lookup by filename
    by_name = {r['file']: r for r in results}

    combined = []
    skip_files = set(COMBINE_FILES.keys())

    for r in results:
        filename = r['file']

        if filename in skip_files:
            # This file will be combined with its parent
            continue

        if filename in COMBINE_FILES.values():
            # This is a parent file - find and add child metrics
            child_files = [k for k, v in COMBINE_FILES.items() if v == filename]

            # Start with a copy of parent metrics
            combined_metrics = dict(r)

            for child in child_files:
                if child in by_name:
                    child_metrics = by_name[child]
                    # Add numeric metrics
                    for key in ['total_lines', 'code_lines', 'comment_lines',
                               'elaboration_ms', 'type_checking_ms', 'parsing_ms',
                               'verification_time_ms']:
                        if key in child_metrics and key in combined_metrics:
                            combined_metrics[key] = combined_metrics.get(key, 0) + child_metrics.get(key, 0)

            # Recalculate efficiency
            if combined_metrics.get('elaboration_ms', 0) > 0:
                combined_metrics['efficiency'] = combined_metrics['code_lines'] / combined_metrics['elaboration_ms']

            combined.append(combined_metrics)
        else:
            combined.append(r)

    return combined


def profile_all_files() -> List[Dict[str, any]]:
    """
    Profile all proof files in the PROOFS_DIR.

    Returns:
        List of metric dictionaries, one per file
    """
    # Find all .lean files
    proofs_path = os.path.join(PROJECT_ROOT, PROOFS_DIR)
    files = []

    for filename in os.listdir(proofs_path):
        if filename.endswith('.lean') and filename not in EXCLUDED_FILES:
            filepath = os.path.join(PROOFS_DIR, filename)
            files.append(filepath)

    files.sort()

    # Profile each file
    results = []
    for filepath in files:
        try:
            metrics = profile_file(filepath)
            results.append(metrics)
        except Exception as e:
            print(f"ERROR profiling {filepath}: {e}")

    return results

def calculate_averages(results: List[Dict[str, any]]) -> Dict[str, any]:
    """Calculate average metrics across all files."""
    if not results:
        return {}

    avg = {'file': 'AVERAGE'}

    # Numeric columns to average
    numeric_cols = [
        'total_lines', 'code_lines', 'comment_lines',
        'elaboration_ms', 'type_checking_ms', 'parsing_ms',
        'import_ms', 'tactic_execution_ms', 'simp_ms',
        'interpretation_ms', 'initialization_ms',
        'compilation_IR_ms', 'compilation_LCNF_base_ms',
        'compilation_LCNF_mono_ms', 'linting_ms',
        'instantiate_metavars_ms', 'verification_time_ms',
        'efficiency'
    ]

    for col in numeric_cols:
        values = [r.get(col, 0) for r in results if isinstance(r.get(col), (int, float))]
        if values:
            avg[col] = sum(values) / len(values)
        else:
            avg[col] = 0.0

    # String columns for average
    for col in ['elaboration_str', 'type_checking_str', 'parsing_str']:
        if col in results[0]:
            avg[col] = 'avg'

    return avg

def write_csv(results: List[Dict[str, any]], output_path: str):
    """Write results to CSV file."""
    if not results:
        print("No results to write!")
        return

    # Define column order - publication-ready metrics (Option 1)
    columns = [
        'file',
        'code_lines',
        'elaboration_ms',
        'type_checking_ms',
        'verification_time_ms',
    ]

    with open(output_path, 'w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=columns, extrasaction='ignore')
        writer.writeheader()
        writer.writerows(results)

    print(f"✓ CSV written to: {output_path}")

def write_summary(results: List[Dict[str, any]], output_path: str):
    """Write human-readable summary."""
    with open(output_path, 'w') as f:
        f.write("Lean Proof Verification Performance Report\n")
        f.write("=" * 80 + "\n\n")
        f.write(f"Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"Files analyzed: {len(results) - 1}\n")  # -1 for average row
        f.write(f"Excluded files: {', '.join(EXCLUDED_FILES)}\n\n")

        f.write("Key Metrics\n")
        f.write("-" * 80 + "\n\n")

        # Sort by elaboration time
        sorted_results = sorted(
            [r for r in results if r['file'] != 'AVERAGE'],
            key=lambda x: x.get('elaboration_ms', 0),
            reverse=True
        )

        f.write(f"{'File':<40} {'Lines':<8} {'Elab(ms)':<12} {'Type(ms)':<12} {'Eff':<8}\n")
        f.write("-" * 80 + "\n")

        for r in sorted_results:
            f.write(f"{r['file']:<40} "
                   f"{r['code_lines']:<8.0f} "
                   f"{r['elaboration_ms']:<12.1f} "
                   f"{r['type_checking_ms']:<12.1f} "
                   f"{r['efficiency']:<8.2f}\n")

        # Add average
        avg = [r for r in results if r['file'] == 'AVERAGE'][0]
        f.write("-" * 80 + "\n")
        f.write(f"{'AVERAGE':<40} "
               f"{avg['code_lines']:<8.1f} "
               f"{avg['elaboration_ms']:<12.1f} "
               f"{avg['type_checking_ms']:<12.1f} "
               f"{avg['efficiency']:<8.2f}\n")

        f.write("\n" + "=" * 80 + "\n\n")

        f.write("Totals:\n")
        total_lines = sum(r['total_lines'] for r in sorted_results)
        total_code = sum(r['code_lines'] for r in sorted_results)
        total_elab = sum(r['elaboration_ms'] for r in sorted_results)
        total_type = sum(r['type_checking_ms'] for r in sorted_results)

        f.write(f"  Total lines: {total_lines:,}\n")
        f.write(f"  Total code lines: {total_code:,}\n")
        f.write(f"  Total elaboration: {total_elab:.1f}ms ({total_elab/1000:.2f}s)\n")
        f.write(f"  Total type checking: {total_type:.1f}ms ({total_type/1000:.2f}s)\n")
        f.write(f"  Total verification: {(total_elab+total_type)/1000:.2f}s\n")

    print(f"✓ Summary written to: {output_path}")

def write_latex(results: List[Dict[str, any]], output_path: str):
    """Write LaTeX table for inclusion in papers."""
    with open(output_path, 'w') as f:
        # Sort by elaboration time (exclude AVERAGE row if present)
        sorted_results = sorted(
            [r for r in results if r['file'] != 'AVERAGE'],
            key=lambda x: x.get('elaboration_ms', 0),
            reverse=True
        )

        # LaTeX table header
        f.write("% Lean Proof Verification Metrics\n")
        f.write("% Generated: " + datetime.now().strftime('%Y-%m-%d %H:%M:%S') + "\n")
        f.write("% Usage: \\input{proof_metrics.tex}\n\n")

        f.write("\\begin{table}[htbp]\n")
        f.write("\\centering\n")
        f.write("\\caption{Proof Verification Performance Metrics}\n")
        f.write("\\label{tab:proof-metrics}\n")
        f.write("\\setlength{\\tabcolsep}{8pt}\n")  # Increase column spacing (default is 6pt)
        f.write("\\begin{tabular}{l@{\\hspace{12pt}}r@{\\hspace{12pt}}r@{\\hspace{12pt}}r@{\\hspace{12pt}}r}\n")
        f.write("\\toprule\n")
        f.write("\\textbf{Proof} & ")
        f.write("\\textbf{LOC} & ")
        f.write("\\textbf{Elab} & ")
        f.write("\\textbf{Check} & ")
        f.write("\\textbf{Total} \\\\\n")
        f.write(" & & (ms) & (ms) & (ms) \\\\\n")
        f.write("\\midrule\n")

        # Data rows
        for r in sorted_results:
            # Get human-readable display name
            display_name = get_display_name(r['file'])

            f.write(f"{display_name} & ")
            f.write(f"{r['code_lines']:.0f} & ")
            f.write(f"{r['elaboration_ms']:.1f} & ")
            f.write(f"{r['type_checking_ms']:.1f} & ")
            f.write(f"{r['verification_time_ms']:.1f} \\\\\n")

        f.write("\\bottomrule\n")
        f.write("\\end{tabular}\n")
        f.write("\\end{table}\n")

    print(f"✓ LaTeX table written to: {output_path}")

def main():
    """Main execution function."""
    print("\n" + "=" * 80)
    print("Lean Proof Verification Performance Profiler")
    print("=" * 80 + "\n")

    os.chdir(PROJECT_ROOT)

    # Profile all files
    print("Starting profiling...\n")
    results = profile_all_files()

    if not results:
        print("ERROR: No files profiled!")
        return

    print(f"\n✓ Profiled {len(results)} files successfully\n")

    # Combine results for files that should be merged
    if COMBINE_FILES:
        print("Combining related proof files...")
        combined_results = combine_results(results)
        print(f"  Combined {len(results)} files into {len(combined_results)} entries\n")
    else:
        combined_results = results

    # Calculate averages (for CSV and summary, not LaTeX)
    avg = calculate_averages(combined_results)
    results_with_avg = combined_results + [avg]

    # Write outputs
    write_csv(results_with_avg, OUTPUT_CSV)
    write_summary(results_with_avg, OUTPUT_SUMMARY)
    write_latex(combined_results, OUTPUT_LATEX)  # LaTeX without average

    print("\n" + "=" * 80)
    print("Profiling complete!")
    print("=" * 80 + "\n")

if __name__ == '__main__':
    main()
