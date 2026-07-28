# Experiments

Three studies, all driven from one entry point. Everything here is reproducible from a clean
checkout. The `results/` directories are committed; the `artifacts/` directories are
regenerated on each run and gitignored.

| Study | What it measures | Output |
|---|---|---|
| **scaling** | Proof length in proof steps, VeriPB (cutting planes) against DRAT (resolution), as instances grow | `scaling/results/*.csv`, `*.png` |
| **sbc** | RoundingSat's cost with and without a symmetry-breaking constraint, plus the cost of checking the resulting certificate, both natively and inside Lean | `sbc/results/*.csv` |
| **schur** | The exact Schur numbers S(2), S(3), S(4), each bracketed by a SAT witness and a PB certificate | `schur_exact/results/timings.csv` |

## 1. Requirements

**Lean.** Build the project first:

```bash
lake build
```

This pins PBLean v0.3.1 or later, whose checker is precompiled as the `VeriPBReflect`
library. The symmetry-breaking study's in-Lean checking numbers assume it: with the
precompiled checker, `checkProofBool` runs as native code, roughly 10 to 20 times faster than
the interpreted path. `preflight` warns if the shared object is missing.

**External solvers**, on `PATH` (RoundingSat may instead be given as `$ROUNDINGSAT`):

| Tool | Used by | Required? |
|---|---|---|
| `roundingsat` | all three studies (PB solving) | yes |
| `veripb` | all three studies (certificate elaboration) | yes |
| `cadical`, `drat-trim` | scaling (the DRAT side) | optional, else the row is `TOOL-MISSING` |
| `minizinc` | schur (SAT witnesses) | optional |

**Python** 3.9+, invoked as `python3`. Only `matplotlib` is needed, and only for the scaling
figures. Without it every CSV is still written and the figure step is skipped.

```bash
python3 -m venv .venv && source .venv/bin/activate && pip install matplotlib
```

## 2. Run

Each subcommand preflights first, which checks the tools and builds `checkbench` and PBLean:

```bash
export ROUNDINGSAT=/path/to/roundingsat        # if not on PATH

python3 experiments/run.py preflight            # check tools only
python3 experiments/run.py scaling
python3 experiments/run.py sbc
python3 experiments/run.py schur
python3 experiments/run.py all
```

Add `--smoke` for a quick check. That runs the two smallest instances per family and writes
to gitignored `*.smoke.*` files. You can restrict to families with e.g.
`python3 experiments/run.py sbc php oddcycle`.

Expect the full SBC run to take one to two hours. Some instances without a symmetry-breaking
constraint (Schur `c4n45`, van der Waerden `W(4,3)`) hit the 600 s timeout by design. They
appear as `censored=1` and their speedups are lower bounds. Certificates can reach hundreds
of megabytes; the clique K15 instance without its SBC is about 391 MB.

## 3. What each study produces

### Scaling

Writes `scaling/results/scaling.csv` plus per-family CSVs, `scaling_<fam>.png`,
`scaling_all.png` and `scaling_<fam>.dat`. It measures proof length in proof steps, VeriPB
against DRAT. The study is entirely external, running RoundingSat and veripb against CaDiCaL
and drat-trim, and never checks anything in Lean.

### Symmetry breaking

Writes `sbc/results/sbc_scaling.csv`, one row per instance, aggregated into `sbc_table.csv`.
Render it as a LaTeX table with:

```bash
python3 experiments/lib/latex_table.py
```

Per instance it records RoundingSat's deterministic and wall time, with and without the SBC,
plus two independent checking costs:

- `check_ns` is PBLean's compiled `checkProofBool` on that certificate, measured by the
  `checkbench` executable (`lib/CheckBench.lean`). `check_status` is `OK`, `TIMEOUT` or
  `FALSE`. A `FALSE` means the certificate was rejected, so its timing is never reported as a
  checking cost.
- `pipeline_net_s` is a real `lake build` of one `csp_unsat_file` reflection theorem, net of
  an imports-only baseline. It covers the whole in-Lean certification: reading the
  certificate, compiling it, the `ofReduceBool` native evaluation, and the kernel accept.

### Exact Schur numbers

Writes `schur_exact/results/timings.csv`, timing both pipelines for S(2), S(3) and S(4), and
leaves every generated `.opb` and `.pbp` in `schur_exact/artifacts/`.

Each `S(c)` is bracketed by two facts about the plain CSP `Schur.schur_csp n c`, which is
just bounds plus sum-free triples with no symmetry breaking:

- the lower bound `S(c) ≥ n` comes from a MiniZinc colouring witness, re-checked in the Lean
  kernel by `decide` (`csp_sat_file`);
- the upper bound `S(c) < n+1` comes from a PB UNSAT certificate produced by RoundingSat and
  veripb, then reflected in the kernel via `Lean.ofReduceBool` (`csp_unsat_file`).

Both legs go through the same symmetry-breaking constraint, Law-Lee `value_precedence c`,
proved equisatisfiable in `CSP/L2S/Proofs/SchurValuePrecedence.lean`. Every theorem in
`CSP/L2S/EndToEnd/SchurCertify.lean` is therefore stated about the plain `schur_csp`.

For each `(c, m = n+1)` the upper-bound leg runs three steps:

1. **Dump the OPB from Lean** for the value-precedence instance
   `(Schur.schur_csp m c).addConstraint (value_precedence c)`, giving
   `artifacts/schur_c{c}n{m}.opb` and its variable count (135 for S(4)).
2. **Solve and log** with `roundingsat schur_c{c}n{m}.opb --proof-log=…`. For S(4) this
   reports UNSAT in about 46 s.
3. **Elaborate the kernel certificate** with `veripb --elaborate …`, which reports
   `s VERIFIED UNSATISFIABLE` and produces `artifacts/schur_{c}_{m}_vp_kernel.pbp`. For S(4)
   that file is about 98 MB.

#### Enabling the S(4) upper bound in Lean

S(2) and S(3) build out of the box from committed certificates. The S(4) certificate is far
too large to commit, so its theorems ship disabled. Generate it with:

```bash
python3 experiments/run.py schur     # writes artifacts/schur_4_45_vp_kernel.pbp
```

then remove the `/-` and `-/` around the S(4) block at the end of
`CSP/L2S/EndToEnd/SchurCertify.lean` and rebuild:

```bash
lake build CSP.L2S.EndToEnd.SchurCertify
```

The block loads the certificate with `csp_unsat_file`, so the 98 MB never reaches the parser.
The kernel check runs `checkProofBool` as native code in roughly 70 s. Interpreted, the same
check takes about 21 minutes.

## 4. Regenerating a committed certificate

`experiments/gen_cert.py` regenerates one instance's certificate against the canonical
encoder and commits it under `CSP/L2S/Backends/PB/Problems/certs/`:

```bash
python3 experiments/gen_cert.py <Module> <cspExpr> <out>
```

It prints the OPB variable count, which is the `numVars` argument to `csp_unsat_file`.

## 5. A note on the Lean-side writes

The SBC study writes throwaway modules under `CSP/L2S/Backends/PB/Bench/` (gitignored except
`Generators.lean`) and deletes them afterwards, because `lake build` only kernel-checks
modules under `CSP/`. An interrupted run can leave a `ChkTmp.lean` and a large
`certs/ChkTmp.pbp` behind. Delete them, or a later bare `lake build` will try to kernel-check
that stale certificate.
