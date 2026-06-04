# Adding a new end-to-end UNSAT instance — a playbook

This guide is a complete, self-contained recipe for adding a new kernel-checked
`¬ myCSP.isSatisfiable` theorem to the verified pseudo-Boolean (PB) backend
(`CSP/L2S/Backends/PB/`, namespace `CSP.L2S.PB`). It assumes only that you can
build the project; it does not assume any prior context on the design.

Read the "Verified UNSAT certificates" section of the top-level `README.md` first
for the pipeline and trust boundary. `PLAN.md` has the architecture and the full
list of what is already implemented.

**What you are producing.** For a finite-domain CSP `myCSP : HomogeneousCSP`
(usually a corpus problem from `CSP/L2S/Tests/lean/`), a Lean theorem

```lean
theorem my_unsat : ¬ myCSP.isSatisfiable
```

checked by Lean's kernel. The external PB solver (RoundingSat) and proof
elaborator (veripb) are untrusted: they only ever *produce a certificate string*
that PBLean's verified checker re-validates against the Lean-side constraints. A
wrong certificate causes a *failure to elaborate*, never an unsound theorem.

---

## 0. Prerequisites

1. The project builds: `lake exe cache get && lake build` (ends with
   `Build completed successfully (NNNN jobs)`).
2. `roundingsat` and `veripb` are on your `PATH` (only needed to *generate* the
   certificate; re-checking a committed theorem needs only Lean). Install:
   - RoundingSat — <https://gitlab.com/MIAOresearch/software/roundingsat>
   - veripb (3.0.1) — <https://gitlab.com/MIAOresearch/software/VeriPB>
   The maintainer keeps both in `~/.local/bin`.

---

## 1. The shape of an instance file

Every instance module follows the same seven-part skeleton. (`Pigeonhole.lean` is
the canonical clean example; it is reproduced in full in §4.)

```lean
import CSP.L2S.Backends.PB.Adapter            -- domainValues, bound_sat, the bridges
import CSP.L2S.Backends.PB.Extend             -- csp_unsat_generic (the spine)
import CSP.L2S.Backends.PB.NotAllEqualBridge  -- alldifferent_sat etc. (if needed)
import CSP.L2S.Tests.lean.«NN_my_problem»     -- THE corpus CSP

namespace CSP.L2S.PB.MyProblem
open CSP.L2S CSP.L2S.PB

def mySig : CSPSig := …                        -- (2) the PB signature
def myEncoded : List (PBConstr (PBVar mySig)) := …  -- (3) the encoding
def myKernelProof : String := "…"              -- (4) the external certificate
theorem my_formulaUnsat : … := …              -- (5) checker discharges it
theorem my_unsat : ¬ myCSP.isSatisfiable := … -- (6) the end-to-end theorem

end CSP.L2S.PB.MyProblem
```

> **Co-import rule.** Each `Tests/lean/NN_*.lean` file defines its own `def main`,
> so two instance files that import *different* corpus files **cannot be imported
> into the same Lean module** ("environment already contains 'main'"). That is why
> all reusable bridges live in test-file-free modules (`Adapter`, `Extend`,
> `NotAllEqualBridge`, `CircuitGates`). Keep your instance file importing exactly
> one corpus file.

---

## 2. The recipe, step by step

### Step 1 — Locate and probe the corpus CSP

Find the CSP in `CSP/L2S/Tests/lean/NN_name.lean`. Read its definition: how many
variables (`num_vars`), what the `bound` constraints are (the per-variable
domain), and which constraint patterns it uses (`alldifferent`, `linear_eq`,
`sum_eq`, `at_most_k`, …). Build it once so its olean exists:

```bash
lake build CSP.L2S.Tests.lean.«NN_name»
```

**Confirm it is actually UNSAT before writing any Lean** — do not trust a
corpus comment. Translate it to OPB (see Step 5 for the dump trick) and run
`roundingsat`; it must print `s UNSATISFIABLE`. (A corpus bug once made a "S(2)=4
UNSAT" file silently SAT.) If you need an UNSAT *variant* of a satisfiable corpus
CSP (e.g. add contradictory givens), build it with `HomogeneousCSP.addConstraints`
— see the gotcha in §6.

### Step 2 — Write the signature `mySig : CSPSig`

`CSPSig` is the encoder's variable signature: integer-variable count `nInt`, plus
`nBool`/`nAux` (usually `0`), and a finite domain per integer variable.

```lean
def mySig : CSPSig where
  nInt := <num_vars>
  nBool := 0
  nAux := 0                     -- > 0 only for Big-M ≠ / Tseitin (auxiliary vars)
  values := fun _ => domainValues lb ub        -- the integer interval [lb, ub]
  sorted := fun _ => domainValues_sorted lb ub
  nonempty := fun _ => domainValues_nonempty (by norm_num)
```

`domainValues lb ub : List ℤ` is the sorted list `[lb, …, ub]`; the two proof
fields are discharged by the matching `domainValues_*` lemmas (`Adapter.lean`).
If different variables have different domains, make `values` a `fun i => …` that
cases on `i` instead of a constant.

> **Domain width matters.** A domain `[c, c+1]` (e.g. Booleans `{0,1}`) has
> *width 1* — a single threshold per variable — so `mySig.monotonicity` is
> **empty** and the encoding is small. Wider domains give non-empty monotonicity
> (the staircase clauses `tⱼ₊₁ + ¬tⱼ ≥ 1`).

### Step 3 — Encode the constraints (reuse an existing encoder)

Build `myEncoded : List (PBConstr (PBVar mySig))` as the monotonicity clauses
plus your constraints, normalized:

```lean
def myEncoded : List (PBConstr (PBVar mySig)) :=
  mySig.monotonicity ++ (encodeAllDifferent myVars [1, 2]).filterMap normalize
```

Pick the encoder that matches the corpus constraint (see §5 for the full list).
`normalize` turns the encoder's signed PB constraints into PBLean-shaped natural
ones; some normalize to `none` (tautologies over the domain) and are dropped by
`filterMap normalize` — that is expected and harmless.

You do **not** write a new encoder for a supported family; you reuse one. Adding a
brand-new constraint family (a new encoder + soundness lemma) is a larger task,
out of scope for this playbook.

### Step 4 — Generate the external certificate (RoundingSat + veripb)

See §5 below for the exact commands. The output is a VeriPB *kernel* proof
(version 3.0); paste it verbatim into a `String` literal `myKernelProof`.

### Step 5 — Discharge `formulaUnsat` via the checker

```lean
theorem my_formulaUnsat :
    VeriPB.Reflect.formulaUnsat (myEncoded.toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ <numVars> myKernelProof (by native_decide)
```

`<numVars>` is the OPB variable count (the `#variable=` in the OPB header — equal
to `mySig`'s total threshold + bool + aux variables). `native_decide` runs
PBLean's verified checker on the embedded proof string. This is the *only*
`native_decide` in the file and the one place the certificate enters.

> The committed instances all embed the kernel proof as a string and call
> `checkProof_sound` directly, as above. (There is also a `csp_reflect_unsat name
> cs numVars "file.pbp"` command that reads the proof from a committed file, and a
> non-hermetic `csp_decide` that shells out to the solvers at elaboration time —
> both in `Tactic.lean` — but the inline-string form is what every theorem in the
> README table uses, and it is fully reproducible from Lean alone.)

### Step 6 — The end-to-end theorem

Compose a CSP solution → in-domain values + constraint facts → PB model →
contradiction with the certificate. Use one of the two spines (§3). The pattern:

1. `rintro ⟨a, hsol⟩` — assume a solution `a`.
2. Prove every variable is in its declared domain (from the corpus `bound`s, via
   `bound_sat` + `mem_domainValues`).
3. Extract the corpus constraint facts you need (via the pattern→fact bridges, §5).
4. Apply the spine with your encoded constraints, supplying the per-constraint
   `extend_sat_*` soundness lemmas; close with `my_formulaUnsat`.

### Step 7 — Confirm the trust boundary

```bash
echo 'import CSP.L2S.Backends.PB.MyProblem
#print axioms CSP.L2S.PB.MyProblem.my_unsat' > /tmp/chk.lean
lake env lean /tmp/chk.lean
```

It must print exactly:

```
[propext, Classical.choice, Quot.sound,
 CSP.L2S.PB.MyProblem.my_formulaUnsat._native.native_decide.ax_1_1]
```

— the three standard axioms plus one `native_decide` axiom. **No `sorryAx`.** If
`sorryAx` appears, a proof is incomplete.

---

## 3. The two spines

### `csp_unsat_generic` (`Extend.lean`) — the general spine

```lean
theorem csp_unsat_generic (S : CSPSig)
    (userConstrs : List (PBConstr (PBVar S)))
    (P : (Fin S.nInt → Int) → (Fin S.nBool → Bool) → Prop)
    (auxOf : (Fin S.nInt → Int) → (Fin S.nBool → Bool) → (Fin S.nAux → Bool))
    (hsound : ∀ a bA, (∀ i, a i ∈ S.values i) → P a bA →
        ∀ c ∈ userConstrs, c.sat (extend a bA (auxOf a bA)))
    (hunsat : VeriPB.Reflect.formulaUnsat
      ((S.monotonicity ++ userConstrs).toArray.map PBConstr.toNatConstr)) :
    ¬ ∃ a bA, (∀ i, a i ∈ S.values i) ∧ P a bA
```

You supply: the PB constraints `userConstrs` (without monotonicity — the spine
prepends and discharges it), a solution predicate `P a bA` (the facts a CSP
solution gives you, e.g. `(myVars.map a).Nodup`), an aux-setter `auxOf` (use
`fun _ _ _ => false` for aux-free encodings), and `hsound` (each user constraint
holds under `extend a bA (auxOf a bA)` — discharged by the `extend_sat_*`
lemmas). This spine is needed when the encoding allocates auxiliary variables
(Big-M `≠`, Tseitin gates), since it lets `auxOf` set them from the solution.

### `unsat_of_pb` (`Adapter.lean`) — the clean linear-list route

```lean
theorem unsat_of_pb (csp : HomogeneousCSP) (lb ub : Fin csp.num_vars → ℤ)
    (hle : ∀ i, lb i ≤ ub i)
    (hbound : ∀ i, bound i (lb i) (ub i) ∈ csp.constraints)
    (lin : List (List (Int × Fin csp.num_vars) × Int))
    (hlin : ∀ a, csp.isSolution a → ∀ c ∈ lin, (c.1.map (fun p => p.1 * a p.2)).sum ≤ c.2)
    (hunsat : VeriPB.Reflect.formulaUnsat
        ((encodeLinear (toCSPSig csp lb ub hle) lin).toArray.map PBConstr.toNatConstr)) :
    ¬ csp.isSatisfiable
```

When the whole problem is linear `≤`-constraints over a uniform interval domain
(e.g. Paley independent set: each edge is `xᵤ + xᵥ ≤ 1`, the size bound is
`Σ −xᵢ ≤ −k`), this is shorter than `csp_unsat_generic`: you give the bounds,
the membership proof `hbound`, the linear list `lin` (each entry a
`(terms, rhs)` pair meaning `Σ coeff·var ≤ rhs`), and `hlin` deriving each from a
solution. The adapter builds the `CSPSig` and the encoding for you.

---

## 4. A fully worked example: pigeonhole (`Pigeonhole.lean`)

`php_3_2` (corpus `35_pigeonhole.lean`) is three pigeons into two holes with an
`alldifferent` — infeasible because three distinct values cannot fit in a
two-value domain. Here is the complete instance, annotated.

```lean
import CSP.L2S.Backends.PB.Adapter
import CSP.L2S.Backends.PB.AllDifferent
import CSP.L2S.Backends.PB.Extend
import CSP.L2S.Backends.PB.NotAllEqualBridge
import CSP.L2S.Tests.lean.«35_pigeonhole»

namespace CSP.L2S.PB.Pigeonhole
open CSP.L2S CSP.L2S.PB

-- (2) Signature: 3 integer vars (pigeons), each over the hole domain {1,2}.
def phpSig : CSPSig where
  nInt := 3
  nBool := 0
  nAux := 0
  values := fun _ => domainValues 1 2
  sorted := fun _ => domainValues_sorted 1 2
  nonempty := fun _ => domainValues_nonempty (by norm_num)

-- The alldifferent scope (Vector.ofFn id = [0,1,2]) and its List form.
def phpScope : _root_.Vector (HomogeneousVarIndex 3) 3 := _root_.Vector.ofFn id
def phpVars : List (Fin phpSig.nInt) := phpScope.toList

-- (3) Encoding: (empty) monotonicity ++ normalized alldifferent over {1,2}.
def phpEncoded : List (PBConstr (PBVar phpSig)) :=
  phpSig.monotonicity ++ (encodeAllDifferent phpVars [1, 2]).filterMap normalize

-- (4) The externally generated kernel proof (RoundingSat + veripb), embedded.
def phpKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 2;
rup >= 0 : ~ ;
pol 3 1 1000000000000000 * + 2 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 4;
end pseudo-Boolean proof;
"

-- (5) The verified checker discharges formulaUnsat (3 = OPB var count: x1,x2,x3).
theorem php_formulaUnsat :
    VeriPB.Reflect.formulaUnsat (phpEncoded.toArray.map PBConstr.toNatConstr) :=
  VeriPB.Reflect.checkProof_sound _ 3 phpKernelProof (by native_decide)

-- (6) The end-to-end theorem.
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiable := by
  rintro ⟨a, hsol⟩
  -- 6.2: every pigeon's value lies in {1,2}, from its `bound` constraint.
  have hdom : ∀ i : Fin phpSig.nInt, a i ∈ phpSig.values i := by
    intro i
    have hb : HomogeneousCSP.satisfiesConstraint (bound i 1 (2 : ℕ)) a := by
      apply hsol
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    obtain ⟨h1, h2⟩ := bound_sat i 1 (2 : ℕ) a hb
    have h2' : a i ≤ 2 := by exact_mod_cast h2
    show a i ∈ domainValues 1 2
    exact mem_domainValues.mpr ⟨h1, h2'⟩
  -- 6.3: the pigeon values are pairwise distinct, from the `alldifferent`.
  have hnodup : (phpVars.map a).Nodup := by
    have ha : HomogeneousCSP.satisfiesConstraint (php_alldiff 3) a :=
      hsol _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
    exact alldifferent_sat phpScope a ha
  -- 6.4: the spine rules out any in-domain, pairwise-distinct solution.
  have key : ¬ ∃ (a : Fin phpSig.nInt → Int) (_ : Fin phpSig.nBool → Bool),
      (∀ i, a i ∈ phpSig.values i) ∧ (phpVars.map a).Nodup := by
    apply csp_unsat_generic phpSig
      ((encodeAllDifferent phpVars [1, 2]).filterMap normalize)
      (fun a _ => (phpVars.map a).Nodup)
      (fun _ _ _ => false)                       -- aux-free: auxOf = false
    · intro a' bA hdom' hnodup' c hc             -- hsound, per constraint
      exact extend_sat_encodeAllDifferent a' bA _ hdom' phpVars [1, 2] c hc hnodup'
    · exact php_formulaUnsat                      -- hunsat
  exact key ⟨a, fun _ => false, hdom, hnodup⟩
```

**How the pieces line up.** `bound_sat` turns the corpus `bound` into
`1 ≤ a i ≤ 2`; `alldifferent_sat` turns the corpus `alldifferent` into the
`Nodup` predicate `P`; `csp_unsat_generic` (with `auxOf = false`) needs only that
each normalized `encodeAllDifferent` constraint holds under `extend`, which is
exactly `extend_sat_encodeAllDifferent`; and `php_formulaUnsat` supplies the
kernel-checked contradiction. To scale to `php_5_4` (5 pigeons, 4 holes) only
`nInt`, the domain `1 4`, the variable list, the encoding's value list
`[1,2,3,4]`, and the certificate change — the proof structure is identical (see
the second half of `Pigeonhole.lean`).

---

## 5. Reference: reusable encoders and bridges

### Generating the OPB and the certificate

To dump the OPB for an encoding, add a temporary import and `#eval` to your file
and run it (`toOPBString` lives in `Serialize.lean`, which most instance files do
not otherwise import):

```lean
import CSP.L2S.Backends.PB.Serialize           -- temporary; for the OPB dump only

-- temporary; delete after generating the certificate
#eval IO.println (toOPBString
  ((mySig.monotonicity ++ myUserConstraints).toArray.map PBConstr.toNatConstr) <numVars>)
```

```bash
lake env lean CSP/L2S/Backends/PB/MyProblem.lean > my.opb   # capture the OPB
roundingsat my.opb --proof-log=my.pbp                       # expect: s UNSATISFIABLE
veripb --elaborate my.kernel.pbp my.opb my.pbp              # expect: s VERIFIED UNSATISFIABLE
```

Paste the contents of `my.kernel.pbp` into `myKernelProof`. The OPB format:
1-based variables (`x1`, `x2`, …; `~x1` is negation), `>=`, every line ends
` ;`, and RoundingSat's full header. Lean var `i` (0-based) ↦ OPB `x{i+1}`.

> **Big-M sentinel gotcha.** Certificates that use Big-M coefficients (the general
> linear `≠` encoder) make RoundingSat emit a `;18446744073709551615` (u64-max)
> RUP hint that veripb 3.0.1 cannot parse ("Constraint ID parsing error"). Fix:
> `roundingsat my.opb --proof-log=my.pbp --log-debug=0` then strip the sentinel
> before elaborating:
> ```bash
> sed 's/;18446744073709551615/;/g' my.pbp > my.clean.pbp
> veripb --elaborate my.kernel.pbp my.opb my.clean.pbp
> ```
> Small-coefficient certificates (alldifferent, cardinality, AND/OR circuits) do
> not trigger this.

> **Trust roundingsat's stdout, not its exit code.** RoundingSat exits 0 even on a
> bad header or a SAT result. Grep its output for the exact string
> `s UNSATISFIABLE` (note `SATISFIABLE` is a substring of `UNSATISFIABLE`, so match
> the leading `s `).

### Encoders (in `Encode.lean`, `AllDifferent.lean`, `Cardinality.lean`, `LinearNe.lean`, `NotAllEqual.lean`)

| Encoder | Encodes | Aux? | Per-constraint soundness lemma |
|---------|---------|------|--------------------------------|
| `encodeLinearLe terms b` | `Σ aᵢ xᵢ ≤ b` | no | `extend_sat_encodeLinearLe` |
| `encodeLinearEq / Ge / Lt / Gt` | `=, ≥, <, >` (wrappers over `≤`) | no | (via `encodeLinearLe`) |
| `encodeAllDifferent vars D` | `alldifferent` (per-value cardinality over value list `D`) | no | `extend_sat_encodeAllDifferent` |
| `encodeNeConst j val` | `xⱼ ≠ val` | no | `extend_sat_encodeNeConst` |
| `encodeAtMostK / AtLeastK / ExactlyK` | cardinality over Boolean vars | no | (linear-list route, or `extend_sat_encodeLinearLe`) |
| `encodeNotAllEqualBin vars` | not-all-equal, binary domain | no | `extend_sat_encodeNotAllEqualBin` |
| `encodeNotAllEqualMulti vars D` | not-all-equal, multi-valued | no | `extend_sat_encodeNotAllEqualMulti` |
| `encodeLinearNe terms b s` | general `Σ aᵢ xᵢ ≠ b` (Big-M, fresh aux `s`) | **yes** | `extend_sat_encodeLinearNe` |

For circuits, `CircuitGates.lean` provides `{nv}`-generic gate bridges
(`xor_all3_sat`, `and_gate_sat`, `or_all3_full_sat`, and the pure-ℤ full-adder
identity `fa_identity`). AND/OR/2-input-XOR over `{0,1}` are *linear* and ride
`encodeLinearLe`; 3-input parity is captured by `fa_identity`. No Tseitin/BoolExpr
machinery is needed for any committed circuit instance.

### Pattern → fact bridges (turn a satisfied corpus constraint into a usable fact)

| Bridge | Module | From corpus constraint | Gives |
|--------|--------|------------------------|-------|
| `bound_sat` | `Adapter` | `bound v lb ub` | `lb ≤ a v ∧ a v ≤ ub` |
| `linear_le_sat` | `Adapter` | `linear_le scope coeffs t` | `Σ coeffᵢ·a vᵢ ≤ t` |
| `linear_eq_sat` | `Adapter` | `linear_eq …` | `Σ … = t` |
| `linear_ne_sat` | `Adapter` | `linear_ne …` | `Σ … ≠ t` |
| `sum_eq_sat` | `Adapter` | `sum_eq scope t` | `(scope.map a).sum = t` |
| `at_most_k_sat` | `Adapter` | `at_most_k scope k` | `(scope.map a).sum ≤ k` |
| `at_least_k_sat` | `Adapter` | `at_least_k scope k` | `k ≤ (scope.map a).sum` |
| `alldifferent_sat` | `NotAllEqualBridge` | `alldifferent scope` | `(scope.map a).Nodup` |
| `not_equal_sat` | `NotAllEqualBridge` | `not_equal v1 v2` | `a v1 ≠ a v2` |
| `not_equals_const_sat` | `NotAllEqualBridge` | `ne_const v c` | `a v ≠ c` |
| `equals_const_sat` | `NotAllEqualBridge` | `equals_const v c` (givens) | `a v = c` |
| `schur_triple_sat` | `NotAllEqualBridge` | `schur_triple v1 v2 v3` | not-all-equal of the three |

---

## 6. Known gotchas (read before you start)

- **`(0 : Fin mySig.nInt)` fails to synthesize `OfNat`.** The `nInt` projection is
  opaque to instance search. Write the literal at the concrete type instead:
  `(0 : Fin 3)` (it is *defeq* to `Fin mySig.nInt`). This applies everywhere you
  write a `Fin`-typed index against a `sig`-derived count — variable indices, aux
  selectors, `hdom (k : Fin N)`.

- **`omega` cannot see through `HomogeneousDomain`.** `HomogeneousAssignment n =
  Fin n → HomogeneousDomain`, and `HomogeneousDomain` is an abbrev for `ℤ` that
  `omega` will *not* unfold for the values `a i` (it treats `a i` as an opaque
  atom — symptom: "No usable constraints found", or it silently drops a bound).
  - For **linear** facts on the corpus side, use `linarith` (it resolves the ring
    instance through the abbrev).
  - For `%` / `≠` / parity / disjunctive facts, prove a **pure-ℤ helper lemma**
    (`(X Y : ℤ) … : … := by omega`) and apply it to the `a i` values directly —
    they are defeq `ℤ`, so it typechecks and the conclusion matches the goal.
  - On the **spine side** the assignment is `a : Fin n → Int` (genuine `Int`), so
    `omega` works there without trouble.

- **Building an UNSAT *variant* of a SAT corpus CSP** (e.g. contradictory givens):
  use `HomogeneousCSP.addConstraints csp newConstrs` (dot-notation), **not**
  `⟨n, csp.constraints ++ […]⟩`. The latter fails because `csp.constraints :
  List (TaggedConstraint csp.num_vars)` will not unify with a `List
  (TaggedConstraint <literal>)` for `HAppend` (instance search does not reduce
  `num_vars` to the literal, and a type ascription does not change the term).
  `addConstraints` keeps everything at `csp.num_vars` and *prepends*
  `newConstrs ++ csp.constraints`.

- **Corpus membership for computed constraint lists** (built with `flatMap` /
  `filterMap` / `dite`): a lemma generic over the loop variables is usually a dead
  end (e.g. `listToFinVector [↑u,↑v] N` will not reduce for *variable* `u,v`).
  Instead prove the *whole list* equal to an explicit `map` by `rfl` — the
  concrete generator over a concrete range reduces definitionally:
  ```lean
  theorem corpus_edges_eq :
      my_edge_constraints N = myEdges.map (fun p => at_most_k ⟨#[p.1, p.2], rfl⟩ 1) := rfl
  ```
  Then membership is uniform: `rw [corpus_edges_eq]; exact List.mem_map.mpr ⟨p, hp, rfl⟩`.
  For small concrete instances the *builder itself* often reduces by `rfl` to an
  explicit list — probe with `example : myCSP.constraints = [...] := by rfl` and, if
  it holds, navigate membership with `show … ∈ [explicit]; List.mem_append_left/right`
  and `List.mem_cons_self` / `List.mem_cons_of_mem`.

- **Flattening a many-constraint solution hypothesis.** To turn `hsol : isSolution
  a` into per-constraint hypotheses without navigating membership constraint by
  constraint:
  ```lean
  rintro ⟨a, hsol⟩
  unfold HomogeneousCSP.isSolution myCSP at hsol      -- MUST unfold isSolution too
  simp only [List.append_assoc, List.cons_append, List.nil_append,
             List.forall_mem_append, List.forall_mem_cons] at hsol
  obtain ⟨hbounds, hc0, …, hlast, _⟩ := hsol           -- trailing _ for the `∀ x ∈ []`
  ```
  `append_assoc` re-associates the left-nested corpus `++` into one flat cons-list
  so `forall_mem_cons` peels off a clean right-nested conjunction.

- **`simp only [myUserList, List.mem_append]` over-evaluates** `encodeAllDifferent`
  into its per-value internals and breaks a flat `rcases`. Use `unfold myUserList
  at hc; rw [List.mem_append, …] at hc` instead, then `rcases`.

- **A literal `Vector`'s `.toList` does not reduce under `simp only`.** When a
  bridge hands you `(⟨#[…], rfl⟩ : Vector …).toList`, use bare `simp` / `simpa`
  (which knows the `Vector`/`Array.toList` lemmas), not `simp only […]`.

- **Rebuild the corpus olean after editing a `Tests/lean/NN_*` file.** `lake env
  lean --run` does *not* build imports; imports use the stale olean. Run `lake
  build CSP.L2S.Tests.lean.«NN_*»` first.

---

## 7. After it builds

- `lake build CSP.L2S.Backends.PB.MyProblem` (or a bare `lake build`).
- Confirm the axioms (§ Step 7).
- A bare `lake build` should still print `Build completed successfully` — the
  `.andSubmodules` glob means your new module is compiled and re-checked
  automatically.
- Commit. Keep the message brief and free of tooling attribution; mirror the
  existing `PB: end-to-end UNSAT for …` commit style.
