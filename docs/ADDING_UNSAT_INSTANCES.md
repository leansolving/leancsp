# Adding a new end-to-end UNSAT instance — a playbook

This guide is a complete recipe for adding a kernel-checked
`¬ myCSP.isSatisfiableInt` theorem to the verified pseudo-Boolean (PB) backend
(`CSP/L2S/Backends/PB/`, namespace `CSP.L2S.PB`). It assumes only that you can
build the project.

**What you are producing.** For a finite-domain CSP `myCSP : IntCSP` (usually a
corpus problem from `CSP/L2S/Tests/lean/`), a Lean theorem

```lean
theorem my_unsat : ¬ myCSP.isSatisfiableInt :=
  csp_unsat_file myCSP <numVars> "certs/my.pbp"
```

checked by Lean's kernel. RoundingSat (the PB solver) and veripb (the proof
elaborator) are untrusted — they only *produce a certificate*, which PBLean's
verified checker re-validates against the Lean-side constraints. A wrong
certificate causes a *failure to elaborate*, never an unsound theorem.

> **Old vs new.** Earlier instances wrote a bespoke `CSPSig`, a hand-rolled
> encoding, per-constraint soundness bridges, and a multi-step proof assembly.
> That is gone. If `myCSP` uses only the supported fragment, the instance is one
> line over a committed certificate file, and the generic `csp_unsat` theorem
> (`GenericEncode.lean`) supplies all the soundness.

---

## 0. Prerequisites

1. The project builds: `lake exe cache get && lake build`.
2. To *generate* a certificate (not to re-check a committed one) you need
   `roundingsat` and `veripb`. `scripts/gen_cert.sh` looks for roundingsat at
   `/home/pablo/projects/roundingsat/build/roundingsat`; override with the
   `ROUNDINGSAT` environment variable. `veripb` must be on `PATH`.

## 1. Probe the corpus CSP

Find the CSP in `CSP/L2S/Tests/lean/NN_name.lean`. Check `num_vars`, the `bound`
constraints (per-variable domain), and which constraint families it uses. Build
it once so its olean exists:

```bash
lake build CSP.L2S.Tests.lean.«NN_name»
```

**Confirm it is in the supported fragment** (see §4). If it uses a family that
`encodePattern` does not yet handle (`alldifferentOffset`, gates, `linear_ne`),
that family must be wired in first — see "Next steps" in the top-level `README.md`;
that is encoder work, not per-problem work.

## 2. Generate the certificate

```bash
scripts/gen_cert.sh <Module> <cspExpr> <out>
```

- `<Module>` — the module defining the CSP, e.g. `CSP.L2S.Tests.lean.«02_color»`
  or, if the CSP is defined in an instance file, that module
  (e.g. `CSP.L2S.Backends.PB.Problems.Sudoku`; build it first so its olean exists).
- `<cspExpr>` — a Lean term of type `IntCSP`, e.g. `k3_2col` or `"langford_2n_csp 2"`.
- `<out>` — certificate base name → `CSP/L2S/Backends/PB/Problems/certs/<out>.pbp`.

The script dumps the canonical encoding `(cspSig csp).monotonicity ++
EncConstr.combine (encodeCSP csp)` to OPB via `toOPBString`, runs RoundingSat and
veripb, commits the elaborated kernel proof, and prints `numVars=<N>` (the OPB
`#variable=` count = `Σ (cspSig csp).width`). Internally:

```bash
lake env lean <dump>.lean > my.opb              # the OPB of encodeCSP csp
roundingsat my.opb --proof-log=my.pbp           # expect: s UNSATISFIABLE
veripb --elaborate certs/my.pbp my.opb my.pbp   # expect: s VERIFIED UNSATISFIABLE
```

> **Big-M sentinel gotcha.** Certificates from the general linear `≠` encoder make
> RoundingSat emit a `;18446744073709551615` RUP hint veripb cannot parse. If you
> extend the script for `linear_ne`, run roundingsat with `--log-debug=0` and
> `sed 's/;18446744073709551615/;/g'` the proof before elaborating.

> **Trust roundingsat's stdout, not its exit code** — it exits 0 even on SAT or a
> bad header. Match the exact string `s UNSATISFIABLE`.

## 3. Write the instance

```lean
import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«NN_name»            -- exactly one corpus file (the `main` clash rule)

namespace CSP.L2S.PB.MyProblem
open CSP.L2S CSP.L2S.PB

theorem my_unsat : ¬ myCSP.isSatisfiableInt :=
  csp_unsat_file myCSP <numVars> "certs/my.pbp"

end CSP.L2S.PB.MyProblem
```

`csp_unsat_file csp numVars "certs/my.pbp"` expands to
`csp_unsat csp (checkProof_sound _ numVars (include_str "certs/my.pbp") (by native_decide))`.
The `include_str` path is relative to *this* `.lean` file, so use `"certs/…"`.
The `hbound` side goal (every variable has its `bound` constraint) is discharged
automatically by `decide`. If the CSP is defined in the instance file rather than a
test file, keep that `def` and import only `GenericEncode` (+ `CSP.L2S.Constraints`
if you use smart constructors).

> **Co-import rule.** Each `Tests/lean/NN_*.lean` defines its own `def main`, so an
> instance file may import at most one corpus file.

## 4. Supported fragment

`encodePattern` (`GenericEncode.lean`) handles, fully automatically:

`bound` · `alldifferent` · `not_equal` / `eq_const` / `ne_const` · `at_most_k` /
`at_least_k` · `linear` (`≤ ≥ < > =`) · `sum` (`≤ ≥ < > =`) · `schur_triple`.

Unsupported constructors encode to `[]` — *sound by weakening* (dropping a
constraint only makes the PB formula easier), but then the certificate will not be
UNSAT and `native_decide` will reject it, so every constraint your instance relies
on for infeasibility must be in the list above.

## 5. Confirm the trust boundary

```bash
echo 'import CSP.L2S.Backends.PB.Problems.MyProblem
#print axioms CSP.L2S.PB.MyProblem.my_unsat' > /tmp/chk.lean
lake env lean /tmp/chk.lean
```

Must print exactly `propext, Classical.choice, Quot.sound, Lean.ofReduceBool,
Lean.trustCompiler` — the three standard axioms plus the two reflection axioms
(`csp_unsat_file` builds the `ofReduceBool` proof term directly, so the axiom is stable and
nameable, not a fresh per-theorem `._native.native_decide.ax`). **No `sorryAx`.**

## 6. Adding a new constraint family

This is the only place per-*family* work happens (never per-problem):

1. Add (or reuse) an encoder + soundness lemma in `Encode.lean` / `AllDifferent.lean`
   / `Cardinality.lean` / `LinearNe.lean` / `NotAllEqual.lean`, exposed as an
   `enc<Pattern> : … → EncConstr S` in `Library.lean`.
2. Add one case to `encodePattern` (converting the pattern's `ℕ` indices to
   `Fin S.nInt` with `toFinList`, guarded by a decidable in-range check).
3. Add the matching case to `encodePattern_sound` (derive the encoder's `pre` from
   `patternHolds`) and `encodePattern_setsAux` (aux-freeness, or aux handling).
4. For aux-using families (`linear_ne`), switch `csp_unsat` from
   `csp_unsat_of_encfree` to `csp_unsat_of_enc_alloc` and size `cspSig.nAux`.

After that, every instance using the family is a one-liner. See the worked
`linear`/`sum`/`schur_triple` cases in `GenericEncode.lean` for the pattern.
