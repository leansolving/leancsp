# Schur exact values S(2)–S(4): both pipelines, self-contained

Pins the Schur numbers up to S(4) at the **CSP level**, bracketing each `S(c)` by two facts about
the *original simple* CSP `Schur.schur_sb n c` (bounds + sum-free triples, no symmetry breaking):

* **lower bound** `S(c) ≥ n` — a MiniZinc value-precedence colouring witness, re-checked in the
  Lean kernel by `decide` (`csp_sat_file`);
* **upper bound** `S(c) < n+1` — a pseudo-Boolean UNSAT certificate (roundingsat → veripb),
  reflected in the kernel via `Lean.ofReduceBool` (`csp_reflect_unsat_csp` / `csp_unsat_file`).

Both legs run through the same symmetry-breaking constraint (Law–Lee `value_precedence c`, proved
equisatisfiable in `CSP/L2S/Proofs/SchurValuePrecedence.lean`), so every theorem is about the plain
`schur_sb`. The certified theorems live in `CSP/L2S/EndToEnd/SchurCertify.lean` (S(2), S(3)) and
`CSP/L2S/EndToEnd/Schur4Upper.lean` (S(4)).

## Layout

```
experiments/schur_exact/
  results/timings.csv     # committed: one representative wall-clock per stage
  artifacts/              # gitignored, regenerable: *.opb, *.pbp, and the ~98 MB S(4) kernel cert
```

The S(4) upper-bound certificate is **~98 MB** — too large to commit — so it is **not** in git; it
is regenerated on demand into `artifacts/` (see below). `CSP/L2S/EndToEnd/Schur4Upper.lean` reads it
from `experiments/schur_exact/artifacts/schur_4_45_vp_kernel.pbp`, so that module only builds after
the cert has been generated locally.

## Reproduce

Prerequisites on `PATH`: `lake` (this toolchain), `roundingsat`, `veripb`, and `minizinc`
(with Gecode + Chuffed). From the repo root:

```sh
python experiments/run_schur_exact.py
```

This times **both** pipelines for S(2)/S(3)/S(4), writes `results/timings.csv`, and leaves every
generated `.opb`/`.pbp` in `artifacts/` — including the S(4) kernel cert the Lean module needs.

### The UNSAT pipeline (upper bound `S(c) < n+1`) — how the cert is made

For each `(c, m=n+1)` the script runs exactly these steps (all in `experiments/lib/harness.py`,
driven from `run_schur_exact.py`):

1. **Dump the OPB from Lean** — `#eval toOPBString` of the value-precedence instance
   `(Schur.schur_sb m c).addConstraint (value_precedence c)`, giving `artifacts/schur_c{c}n{m}.opb`
   and the variable count (135 for S(4)).
2. **Solve + log** — `roundingsat schur_c{c}n{m}.opb --proof-log=schur_{c}_{m}_vp.pbp`
   (S(4): reports UNSAT in ~46 s, ~5.4×10⁵ conflicts).
3. **Elaborate the kernel certificate** — `veripb --elaborate schur_{c}_{m}_vp_kernel.pbp
   schur_c{c}n{m}.opb schur_{c}_{m}_vp.pbp` → `s VERIFIED UNSATISFIABLE`, producing
   `artifacts/schur_{c}_{m}_vp_kernel.pbp` (S(4): ~98 MB).

That final `schur_4_45_vp_kernel.pbp` is what `Schur4Upper.lean` loads and re-checks in the Lean
kernel (via `checkProofBool` + `ofReduceBool`). A wrong cert makes `checkProofBool` return `false`
against the Lean-side formula, so the theorem fails to elaborate rather than becoming unsound —
roundingsat, veripb, and the `.opb`/`.pbp` files all stay **outside** the trust base.

Only need the S(4) cert (not the full timing run)? Run the script; the S(2)/S(3) legs are seconds,
and the S(4) UNSAT leg (~46 s solve + veripb elaboration) writes the cert to `artifacts/`.

## Building the Lean theorems

```sh
lake build CSP.L2S.EndToEnd.SchurCertify    # S(2)=4, S(3)=13 (committed small certs)
lake build CSP.L2S.EndToEnd.Schur4Upper     # S(4)=44 (needs artifacts/schur_4_45_vp_kernel.pbp)
```

`Schur4Upper.lean` reflects the 98 MB cert without `include_str` (which OOMs the parser at that
size): the command `csp_reflect_unsat_csp` reads it with `IO.FS.readFile` at elaboration. The
kernel check runs the compiled `checkProofBool` **interpreted** here (~21 min); the same check runs
in ~49 s as a native executable (`experiments/lib/CheckBench.lean`, measured in
`experiments/sbc/results/check_largest.csv`). Making the in-Lean check native needs a precompiled
PBLean kernel library (a veripb packaging change), tracked separately.
