#!/usr/bin/env python3
"""Combine translation times and solver times into a single CSV."""

import csv
from collections import defaultdict

def ns_to_ms(ns_str):
    """Convert nanoseconds to milliseconds."""
    if not ns_str:
        return ''
    try:
        return f"{float(ns_str) / 1_000_000:.6f}"
    except ValueError:
        return ''

def s_to_ms(s_str):
    """Convert seconds to milliseconds."""
    if not s_str:
        return ''
    try:
        return f"{float(s_str) * 1000:.6f}"
    except ValueError:
        return ''

def main():
    # Read translation times (all columns)
    translation_data = defaultdict(dict)
    with open('timing_results.csv', 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            problem = row['problem_name']
            backend = row['backend']
            translation_data[problem][backend] = {
                'translation_ns': row['translation_ns'],
                'file_io_ns': row['file_io_ns'],
                'total_translation_ns': str(int(row['translation_ns']) + int(row['file_io_ns'])),
                'file_size_bytes': row['file_size_bytes']
            }

    # Read solver times (using wall_time which includes compilation overhead)
    solver_times = defaultdict(dict)
    with open('solver_benchmark_results.csv', 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            problem = row['problem_name']
            solver = row['solver']
            wall_time = row['wall_time_s'] if row['wall_time_s'] else ''
            solver_times[problem][solver] = wall_time

    # Get all unique problem names (sorted)
    problems = sorted(set(translation_data.keys()) | set(solver_times.keys()))

    # Write combined CSV
    with open('combined_results.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow([
            'problem_name',
            'mzn_translation_ms',
            'mzn_fileio_ms',
            'mzn_total_ms',
            'mzn_size_bytes',
            'chuffed_wall_ms',
            'gecode_wall_ms',
            'smt_translation_ms',
            'smt_fileio_ms',
            'smt_total_ms',
            'smt_size_bytes',
            'z3_wall_ms',
            'cvc5_wall_ms'
        ])

        for problem in problems:
            mzn = translation_data[problem].get('MiniZinc', {})
            smt = translation_data[problem].get('SMT-LIB', {})

            writer.writerow([
                problem,
                ns_to_ms(mzn.get('translation_ns', '')),
                ns_to_ms(mzn.get('file_io_ns', '')),
                ns_to_ms(mzn.get('total_translation_ns', '')),
                mzn.get('file_size_bytes', ''),
                s_to_ms(solver_times[problem].get('Chuffed', '')),
                s_to_ms(solver_times[problem].get('Gecode', '')),
                ns_to_ms(smt.get('translation_ns', '')),
                ns_to_ms(smt.get('file_io_ns', '')),
                ns_to_ms(smt.get('total_translation_ns', '')),
                smt.get('file_size_bytes', ''),
                s_to_ms(solver_times[problem].get('z3', '')),
                s_to_ms(solver_times[problem].get('cvc5', ''))
            ])

    print(f"Combined results written to combined_results.csv ({len(problems)} problems)")
    print("All times in milliseconds (ms)")

if __name__ == '__main__':
    main()
