# Experiments

Three studies, run from one entry point. The `results/` directories are committed; the
`artifacts/` directories are regenerated on each run and gitignored.

| Study | Measures |
|---|---|
| **scaling** | Proof length in proof steps, VeriPB (cutting planes) against DRAT (resolution) |
| **sbc** | Solving cost with and without a symmetry-breaking constraint, and the cost of checking the resulting certificate |
| **schur** | The exact Schur numbers S(2), S(3), S(4) |

## 1. Setup

Build the project first, which also pins the precompiled PBLean checker that the SBC study's
in-Lean timings assume:

```bash
lake build
```

Then put the solvers on `PATH`. RoundingSat may instead be given as `$ROUNDINGSAT`.

| Tool | Used by | Required? |
|---|---|---|
| `roundingsat` | all three studies | yes |
| `veripb` | all three studies | yes |
| `cadical`, `drat-trim` | scaling, DRAT side | optional, else the row is `TOOL-MISSING` |
| `minizinc` | schur, SAT witnesses | optional |

Python 3.9+ as `python3`. `matplotlib` is needed only for the scaling figures; without it the
CSVs and pgfplots `.dat` files are still written and only the figure rendering is skipped.

### Versions used for the paper's experiments

| Tool | Version |
|------|---------|
| RoundingSat | commit `d4edbf7` |
| VeriPB | 3.0.2 |
| CaDiCaL | 1.7.3 |
| MiniZinc | solvers: Gecode for S(2)/S(3), Chuffed for S(4) |

Hardware: AMD Ryzen 5 PRO 8540U, 32 GB RAM; timeout 600 s per solver/checker invocation
(`lib/harness.py`, `lib/scaling_sweep.py`).

Note: PB solving times vary strongly across RoundingSat builds and machines; in particular the
S(4) upper-bound instance (n = 45, solved in ~43 s on the machine above) can exceed the default
600 s timeout elsewhere — raise `TIMEOUT` in `lib/harness.py` if the schur run reports TIMEOUT.

```bash
python3 -m venv .venv && source .venv/bin/activate && pip install matplotlib
```

## 2. Run

```bash
export ROUNDINGSAT=/path/to/roundingsat        # if not on PATH

python3 experiments/run.py preflight            # check tools only
python3 experiments/run.py scaling
python3 experiments/run.py sbc
python3 experiments/run.py schur
python3 experiments/run.py all
```

Each subcommand preflights first, checking the tools and building `checkbench` and PBLean.
Add `--smoke` for a quick pass over the two smallest instances per family, written to
gitignored `*.smoke.*` files. Restrict to families with e.g.
`python3 experiments/run.py sbc php oddcycle`.

The full SBC run takes a few hours. Some instances without a symmetry-breaking constraint
time out by design; those families are flagged `censored=1` in `sbc_table.csv` and their
speedups are lower bounds. Certificates can reach hundreds of megabytes.

## 3. Output

| Study | Files |
|---|---|
| scaling | `scaling/results/scaling.csv`, per-family CSVs, `.dat` and `.png` |
| sbc | `sbc/results/sbc_scaling.csv` per instance, aggregated into `sbc_table.csv` |
| schur | `schur_exact/results/timings.csv` |

Render the SBC table as LaTeX with `python3 experiments/lib/latex_table.py`.

The SBC study records two separate checking costs per instance: `check_ns`, the compiled
`checkProofBool` measured by the `checkbench` executable, and `pipeline_net_s`, a real
`lake build` of one reflection theorem net of an imports-only baseline. A `check_status` of
`FALSE` means the certificate was rejected, so that timing is never a checking cost.

## 4. Enabling the S(4) upper bound

S(2) and S(3) build from committed certificates. The S(4) certificate is too large to commit,
so its theorems ship disabled. To enable them:

```bash
python3 experiments/run.py schur     # writes artifacts/schur_4_45_vp_kernel.pbp
```

Then remove the `/-` and `-/` around the S(4) block at the end of
`CSP/L2S/EndToEnd/SchurCertify.lean` and rebuild:

```bash
lake build CSP.L2S.EndToEnd.SchurCertify
```

## 5. Regenerating a certificate

```bash
python3 experiments/gen_cert.py <Module> <cspExpr> <out>
```

This writes `CSP/L2S/Backends/PB/Problems/certs/<out>.pbp`, overwriting any existing file of
that name, and prints the `numVars` argument to pass to `csp_unsat_file`.

## 6. Note on the Lean-side writes

The SBC study writes throwaway modules under `CSP/L2S/Backends/PB/Bench/` and deletes them
afterwards, because `lake build` only kernel-checks modules under `CSP/`. An interrupted run
can leave a `ChkTmp.lean` and a large `certs/ChkTmp.pbp` behind. Delete them, or a later bare
`lake build` will try to kernel-check that stale certificate.
