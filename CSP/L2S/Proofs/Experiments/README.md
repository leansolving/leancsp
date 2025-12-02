# Experiments

Benchmark and experiment infrastructure for evaluating CSP symmetry breaking, equivalence and the Parity Path Theorem.

## Script-to-Output Mapping

| Script | Outputs | Description |
|--------|---------|-------------|
| `run_experiments.py` | `results/` | Symmetry breaking benchmarks (N-Queens, Graph Coloring, Latin Square) |
| `run_parity_experiments.py` | `parity_results/` | Parity Path Theorem circuit benchmarks |
| `verify_equivalence.py` | `results/equivalence_*.csv` | π-equivalence verification via solution counting |

## Directory Structure

```
Experiments/
├── run_experiments.py           → results/
│                                    ├── detailed_results.csv
│                                    ├── aggregated_results.csv
│                                    └── summary.txt
│
├── run_parity_experiments.py    → parity_results/
│                                    ├── detailed_results.csv
│                                    └── aggregated_results.csv
│
└── verify_equivalence.py        → results/
                                     ├── equivalence_results.csv
                                     └── equivalence_summary.csv
```

**Note:** Problem instances (`.mzn` and `.smt2` files) must be generated first by running the Lean generator files in `CSP/L2S/Proofs/` (e.g., `NQueensSB.lean`, `GraphColoringSB.lean`). These output to `mzn/` and `smt2/` subdirectories.

## Usage

### Symmetry Breaking Experiments

**Step 1: Generate instances** by running the Lean proof files in `CSP/L2S/Proofs/` (e.g., `NQueensSB.lean`, `GraphColoringSB.lean`, `LatinSquareSB.lean`).

**Step 2: Run benchmarks**

```bash
python3 run_experiments.py --runs 5 --timeout 120

# Options:
#   --dry-run     Show what would be tested
#   --runs N      Number of runs per instance (default: 5)
#   --timeout N   Timeout in seconds (default: 120)
#   --include X   Only test instances matching pattern X
#   --exclude X   Skip instances matching pattern X
```

### Parity Path Theorem Experiments

**Step 1: Generate circuit instances** by running `ParityCircuitBenchmarks.lean` (in this folder).

**Step 2: Run experiments**

```bash
python3 run_parity_experiments.py
```

Runs circuits: `and_tree`, `or_tree`, `neg_and_tree`, `neg_or_tree`, `layered`, `majority`

Variants compared: `base` (no fixing) vs `sbc_half` (half inputs fixed)

### Equivalence Verification

```bash
python3 verify_equivalence.py
```

Counts all solutions for equivalent formulations to verify π-equivalence claims.

### Proof Profiling

```bash
python3 profile_proofs.py
```

Extracts metrics from Lean proof files (lines, tactics, complexity).

## Output Formats

### CSV Files

- **detailed_results.csv**: Per-run data with `run_id`, `wall_time`, `solve_time`, `status`
- **aggregated_results.csv**: Statistics per instance: `time_median`, `time_mean`, `time_std`, `time_min`, `time_max`

### Solvers Used

- **MiniZinc**: Gecode, Chuffed
- **SMT**: Z3, CVC5
