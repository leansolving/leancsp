# Certifying Schur numbers S(2)–S(4): both pipelines, timed

This experiment pins the Schur numbers up to S(4) at the **CSP level** and records the
wall-clock of **every stage of both verification pipelines**. Each Schur number is bracketed
by two facts about the *original simple* CSP `Schur.schur_sb n c` (bounds + sum-free triples,
no symmetry breaking):

* a **lower bound** `S(c) ≥ n` = `isSatisfiableInt (schur_sb n c)`, from an external MiniZinc
  colouring witness re-checked in the **Lean kernel** by `decide` (`csp_sat_file`);
* an **upper bound** `S(c) < n+1` = `¬ isSatisfiableInt (schur_sb (n+1) c)`, from a
  pseudo-Boolean UNSAT certificate (roundingsat → veripb → Lean `native_decide`, `csp_unsat_file`).

Both legs run through the **same** symmetry-breaking constraint — Law–Lee `value_precedence c`
— proved equisatisfiable for the Schur CSP in `CSP/L2S/Proofs/SchurValuePrecedence.lean`
(`schur_vp_equisatisfiability'` for SAT, `schur_unsat_of_value_precedence` for UNSAT). The
SBC-extended instance appears only inside each proof; every theorem
(`CSP/L2S/EndToEnd/SchurCertify.lean`) is about the plain `schur_sb`.

## Certification status

| Schur number | Lower `S(c) ≥ n` | Upper `S(c) < n+1` | Verdict |
|---|---|---|---|
| **S(2) = 4**  | ✅ kernel `decide` | ✅ kernel `native_decide` | **exact, fully kernel-verified** |
| **S(3) = 13** | ✅ kernel `decide` | ✅ kernel `native_decide` | **exact, fully kernel-verified** |
| **S(4) = 44** | ✅ kernel `decide` (≥ 44) | ⚠️ external only (< 45) | lower kernel-verified; upper externally verified |

`S(2)=4` and `S(3)=13` are pinned exactly, both directions checked by the Lean kernel.
`S(4) ≥ 44` is kernel-verified; `S(4) < 45` is **externally** verified (roundingsat UNSAT +
veripb VERIFIED) but its certificate is too large to admit into the kernel — see below.

## Timing (one representative run per stage)

`results/schur_exact/timings.csv`. Times in seconds.

### Lower bounds — MiniZinc witness → kernel `decide`

| S(c) | n | solver | solve | kernel `decide` | witness |
|---|---|---|---|---|---|
| 2 | 4  | Gecode  | 0.14 | 0.13 | 8 B |
| 3 | 13 | Gecode  | 0.15 | 0.27 | 26 B |
| 4 | 44 | Chuffed | 7.02 | 2.38 | 88 B |

### Upper bounds — roundingsat → veripb → Lean `native_decide`

| S(c) | n+1 | rsat solve | rsat det-time | conflicts | veripb | cert | Lean check |
|---|---|---|---|---|---|---|---|
| 2 | 5  | 0.004 | 10            | 0       | 0.002 | 277 B  | 0.07 (`native_decide`) |
| 3 | 14 | 0.008 | 3 389         | 31      | 0.003 | 56 KB  | 0.23 (`native_decide`) |
| 4 | 45 | 45.9  | 1 004 177 586 | 535 109 | 2.85  | **102 MB** | — (infeasible) |

The upper-bound difficulty explodes at S(4): roundingsat conflicts jump `0 → 31 → 535 109`
and the certificate `277 B → 56 KB → 102 MB`. The lower bounds, by contrast, stay cheap
(the witness is tiny and the kernel `decide` is seconds even at n=44).

## The S(4) upper bound

Solving it is easy *with* value precedence (it times out without): roundingsat proves
`{1,…,45}` 4-colour-UNSAT in **45.9 s** (1.0 × 10⁹ deterministic ops, 535 109 conflicts) and
veripb elaborates a certificate, `s VERIFIED UNSATISFIABLE`, in **2.85 s**. So `S(4) < 45` is
genuinely **externally verified**.

What blocks a *kernel* proof is certificate size. The veripb kernel certificate is
**101 946 721 bytes (~98 MB, 582 033 lines)** — ~200× the largest cert the reflective
`native_decide` checker has ever digested here (~107 KB), and ~1 800× the S(3) cert. A
direct `native_decide` attempt on it was time-boxed and **killed after ~4 minutes**: the Lean
worker reached 5.8 GB RSS still *parsing the 98 MB `include_str`*, with no elaboration
progress, on a 30 GB host. The bottleneck is not solving or even checking — it is reflecting
a 98 MB term into the kernel (cf. `docs/SCALING.md` §5.1).

The certificate could not be shrunk within the verified pipeline: value precedence is already
the strongest general colour-symmetry SBC available (and is what makes the instance solvable
at all), and roundingsat exposes no proof-size knobs — the cert tracks the 535 k-conflict
cutting-planes search, which is intrinsic to how poorly cutting planes suit Schur. A smaller
kernel certificate would need a fundamentally stronger (and separately verified) symmetry
break or a different proof system. The 98 MB cert is **not committed**.

## Methodology

```
lower  (SAT):  MiniZinc(value-precedence model) --witness.sol--> kernel `decide` (csp_sat_file)
                 --schur_vp_equisatisfiability'.mpr--> isSatisfiableInt (schur_sb n c)
upper (UNSAT):  encodeCSP --OPB--> roundingsat --proof log--> veripb --elaborate--> cert
                 --csp_unsat_file + native_decide--> ¬ isSatisfiableInt (vp instance)
                 --schur_unsat_of_value_precedence--> ¬ isSatisfiableInt (schur_sb (n+1) c)
```

- MiniZinc solve: `harness.timed` around `minizinc --solver …` on a model that mirrors
  `(schur_sb n c).addConstraint (value_precedence c)` exactly (so the witness kernel-checks).
- Kernel `decide`: `lake env lean` wall on the `csp_sat_file` obligation minus an import-only
  baseline.
- roundingsat / veripb: `scripts/sbc_scaling/harness.py` (`run_roundingsat`, `run_veripb`,
  machine-independent `rsat_det_time`).
- `native_decide`: `scripts/sbc_scaling/lean_recheck.py` recheck-minus-baseline wall on the
  committed certificate (run only when the cert ≤ 2 MB).

Witnesses (`csp_sat_file` is untrusted: a wrong witness only fails to elaborate) and PB
certificates (re-checked against the Lean-side formula) are both outside the trust base.
Lower-bound theorems are axiom-clean `[propext, Classical.choice, Quot.sound]`; upper-bound
theorems additionally carry `ofReduceBool` from the PB reflective checker.

## Environment

- AMD Ryzen 5 PRO 8540U (12 threads), 30 GiB RAM
- Lean `leanprover/lean4:v4.30.0`, Mathlib v4.30.0
- roundingsat `d4edbf7`, VeriPB 3.0.2, MiniZinc 2.9.7 (Gecode 6.3.0, Chuffed 0.13.2)

## Reproduce

```sh
# witnesses (value-precedence-respecting colourings)
scripts/gen_sol.sh 4 2 schur_c2_n4 gecode
scripts/gen_sol.sh 13 3 schur_c3_n13 gecode
scripts/gen_sol.sh 44 4 schur_c4_n44 chuffed
# upper-bound certificates (S(2), S(3) only — S(4)'s is ~98 MB, not committed)
scripts/gen_cert.sh CSP.L2S.Proofs.SchurValuePrecedence \
  "(Schur.schur_sb 14 3).addConstraint (value_precedence 3)" schur_3_14_vp
# the certified theorems
lake build CSP.L2S.EndToEnd.SchurCertify
# the timing table
python scripts/schur_exact/run_schur_exact.py   # -> results/schur_exact/timings.csv
```
