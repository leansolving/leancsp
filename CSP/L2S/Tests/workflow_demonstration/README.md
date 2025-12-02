# N-Queens Workflow Demonstration

**Translation vs Solving Time Comparison**

This experiment demonstrates that CSP translation overhead in the L2S framework is negligible compared to solving time, validating the **"prove once, solve many"** workflow efficiency.

## Overview

The workflow:
1. Defines N-Queens CSP in Lean (parameterized)
2. Generates instances for sizes n=10,20,30,...,150 (15 instances)
3. Translates to MiniZinc and SMT-LIB formats
4. Records translation times (~microseconds)
5. Runs 4 solvers (Chuffed, Gecode, Z3, CVC5) with 60s timeout
6. Records solving times (milliseconds to seconds)
7. Compares translation overhead vs solving cost

## Directory Structure

```
workflow_demonstration/
├── README.md                        # This file
├── generate_instances.lean          # Lean instance generator
├── run_workflow.py                  # Orchestration script
├── analyze_results.py               # Visualization script
├── mzn/
│   └── nqueens_*.mzn                # Generated MiniZinc instances
├── smt2/
│   └── nqueens_*.smt2               # Generated SMT-LIB instances
├── results/
│   ├── translation_times.csv        # Translation timing data
│   ├── solver_times.csv             # Solver benchmark results
│   └── combined_analysis.csv        # Combined analysis with ratios
└── plots/
    ├── translation_vs_solving.png   # Dual-axis comparison
    ├── stacked_time_breakdown.png   # Stacked bar chart
    ├── scaling_behavior.png         # Log-log scaling
    └── ratio_summary_table.png      # Ratio table

Timing data (shared with main test suite):
../../timing_results_raw.csv         # Raw timing data (CSP/L2S/Tests/)
```

**Note**: The Lean generator uses custom save functions to write instances directly to `workflow_demonstration/mzn/` and `workflow_demonstration/smt2/`. Timing data is appended to the shared `timing_results_raw.csv` file.

## Running the Workflow

### Prerequisites

- Lean 4 with lake
- Python 3.8+
- MiniZinc with Chuffed and Gecode solvers
- Z3 and CVC5 SMT solvers
- Python packages: pandas, matplotlib, seaborn

### Step 1: Run Complete Workflow

```bash
cd /home/pablo/projects/lean-csp/projects/CSP/CSP/L2S/Tests/workflow_demonstration
python3 run_workflow.py
```

This will:
- Generate 30 instance files (15 sizes × 2 backends)
- Run 120 solver benchmarks (30 instances × 4 solvers)
- Create 3 CSV result files
- **Expected runtime: ~40-50 minutes**

### Step 2: Generate Visualizations

```bash
python3 analyze_results.py
```

This creates 4 plots in the `plots/` directory.

### Manual Execution (Advanced)

If you want to run steps separately:

```bash
# Step 1: Generate instances
cd /home/pablo/projects/lean-csp/projects/CSP
lake env lean --run CSP/L2S/Tests/workflow_demonstration/generate_instances.lean

# Step 2: Run workflow (skips generation)
cd CSP/L2S/Tests/workflow_demonstration
python3 run_workflow.py

# Step 3: Analyze results
python3 analyze_results.py
```

## Expected Results

### Translation Times
- **Constant** across all problem sizes: ~0.5-2ms
- Dominated by file I/O (~0.15-0.20ms)
- Pure translation: ~0.001ms (< 1 microsecond)

### Solving Times
- **Grows exponentially** with problem size
- n=10: ~0.01-0.02s (10-20ms)
- n=50: ~0.5-2s
- n=100: ~5-20s
- n=150: 10-60s (or timeout)

### Translation/Solving Ratio
- **n≤30**: Translation ~1-5% of solving time
- **n≥50**: Translation <0.1% of solving time
- **n≥100**: Translation <0.01% of solving time

**Conclusion**: Translation overhead becomes negligible for realistic problem sizes, validating the efficiency of the "prove once, solve many" approach.

## Output Files

### CSV Results

**translation_times.csv**:
```csv
size,backend,translation_ns,file_io_ns,file_size_bytes
10,MiniZinc,567890,123456,234
10,SMT-LIB,678901,234567,567
...
```

**solver_times.csv**:
```csv
size,solver,backend,status,wall_time_s,solve_time_s,conflicts,propagations,decisions
10,Chuffed,MiniZinc,SAT,0.015,0.012,145,2341,567
10,Gecode,MiniZinc,SAT,0.018,0.014,98,1876,432
...
```

**combined_analysis.csv**:
```csv
size,solver,backend,translation_ms,solving_s,total_s,translation_pct,status
10,Chuffed,MiniZinc,0.567,0.015,0.015,3.78,SAT
20,Chuffed,MiniZinc,0.678,0.145,0.145,0.47,SAT
50,Chuffed,MiniZinc,0.789,2.345,2.346,0.034,SAT
...
```

### Visualizations

**translation_vs_solving.png**:
- Dual-axis line chart
- Left Y-axis: Translation time (ms, linear scale)
- Right Y-axis: Solving time (s, log scale)
- Shows translation is flat while solving grows exponentially

**stacked_time_breakdown.png**:
- Stacked bar chart for each problem size
- Translation (red, tiny sliver at bottom)
- Solving (green, dominant portion)
- Visually demonstrates translation is negligible

**scaling_behavior.png**:
- Log-log plot of solving time vs problem size
- Shows exponential scaling of solving complexity

**ratio_summary_table.png**:
- Table with translation/solving ratios
- Color-coded by threshold (<0.1%, <1%, >1%)
- Highlights when translation becomes negligible

## Implementation Details

### N-Queens CSP Definition

The N-Queens problem is defined in Lean as:

```lean
def nqueens_csp (n : ℕ) : HomogeneousCSP :=
  ⟨n, queens_bounds n ++ [
    alldifferent (_root_.Vector.ofFn id),
    alldifferent_diag_pos n,
    alldifferent_diag_neg n
  ]⟩
```

Variables: n (one per column), domain 1..n (row position)

Constraints:
- All queens in different rows (alldifferent)
- All queens on different positive diagonals
- All queens on different negative diagonals

### Translation Timing

Translation times are measured using `IO.monoNanosNow` in Lean:
- Pure translation time (string generation)
- File I/O time (writing to disk)
- Recorded to `timing_results_raw.csv`

### Solver Benchmarking

Each solver is run with:
- 60-second timeout
- Statistics extraction (conflicts, propagations, decisions)
- Both wall time (Python-measured) and solve time (solver-reported)
- Status capture (SAT, UNSAT, TIMEOUT, ERROR)

### Ratio Calculation

```python
translation_pct = (translation_ns / 1e9) / solving_s * 100
```

Where:
- `translation_ns`: Translation time in nanoseconds
- `solving_s`: Solving wall time in seconds
- Result: Translation as percentage of solving time

## Troubleshooting

### Issue: Lean compilation errors

**Solution**: Ensure you're in the correct directory and have built the project:
```bash
cd /home/pablo/projects/lean-csp/projects/CSP
lake build CSP
```

### Issue: Solver not found

**Solution**: Check solver availability:
```bash
which minizinc
which z3
which cvc5
```

Install missing solvers via package manager or from official sources.

### Issue: Python module errors

**Solution**: Install required packages:
```bash
pip3 install pandas matplotlib seaborn
```

### Issue: Timeout on large instances

**Solution**: This is expected! N-Queens becomes very hard for n>120. Timeouts are captured in the results as `TIMEOUT` status.

## Customization

### Change problem sizes

Edit `SIZES` in `run_workflow.py`:
```python
SIZES = [10, 20, 30, 40, 50]  # Smaller range for quick testing
```

### Change timeout

Edit `TIMEOUT` in `run_workflow.py`:
```python
TIMEOUT = 120  # 2 minutes instead of 1
```

### Test different problems

Modify `generate_instances.lean` to generate different CSP instances:
```lean
def graph_coloring_inst (n : ℕ) : HomogeneousCSP := ...
```

## References

- L2S Framework: `projects/CSP/CSP/L2S/`
- Test Helpers: `projects/CSP/CSP/L2S/Tests/TestHelpersTimed.lean`
- Solver Benchmarks: `projects/CSP/CSP/L2S/Tests/run_solver_benchmarks.py`
- Proof Experiments: `projects/CSP/CSP/L2S/Proofs/Experiments/`

## Contact

For questions or issues, see the main L2S project documentation.
