# Cautionary example: an unsound reversal reformulation of Schur

This note is a precise, self-contained spec for adding the Lean theorems that
back the cautionary example of the paper. It covers **two** obligations that both
fail: the reversal is not a symmetry (`3 ≤ n ≤ 12`), and the strict lex leader is
not a valid symmetry-breaking constraint (the real cause of the false `S(3) < 13`
at `n = 13`). Read the paper subsection first: it is
`\subsection{A cautionary example: an unsound reformulation}` (label
`sec:cautionary`) in `paper.tex`. The headline theorem stated there is

```lean
theorem reversal_not_schur_symmetry :
    ¬ VariableSymmetry (schur 3 3) (reversal 3)
```

and it does **not** yet exist in the repository. The task is to make that
statement real and kernel-checked, and (optionally) to generalize it. Everything
below is written so a future session can implement it without re-deriving the
setup.

## 1. What must be proven, and why (two independent obligations)

The paper transplants a reversal-based symmetry-breaking constraint (the strict
lexicographic leader `x <_lex rev(x)`) from van der Waerden and modular Schur,
where the reversal `i ↦ n+1-i` is a genuine symmetry, onto the ordinary Schur
problem, where it is not. Adding this leader **soundly** through our framework
requires two facts (`sec:symmetry`):

1. **The reversal is a variable symmetry of the Schur CSP, for every `n`**
   (`VariableSymmetry`). *This is false for `3 ≤ n ≤ 12`.* Sections 3–4 formalize
   its refutation.
2. **The leader is a symmetry-breaking constraint for that symmetry**
   (`variableSymmetryBreakingConstraint`): every solution can be mapped, by a
   symmetry, to one that also satisfies the leader. *This is false too, and it is
   the real cause of the false `S(3) < 13`.* Section 5 formalizes its refutation.

Both artifacts are worth having, and they make different points. Obligation 1
fails on a wide range but never produces a wrong answer (solutions survive the
cut). Obligation 2 is what actually breaks at `n = 13`: there reversal *is* a
symmetry (all solutions are palindromes, so it fixes each one), yet a palindrome
can never satisfy the *strict* leader `s <_lex rev(s) = s <_lex s`, and the
symmetry sends it only to itself, so no solution survives and the augmented model
is (wrongly) UNSAT. Neither theorem exists in the repo yet.

The concrete witness for obligation 1 is, at `n = 3` with 3 colors, the solution
`[0,1,1]`, whose reversal `[1,1,0]` colors the numbers `1, 1, 2` alike even though
`1 + 1 = 2`. Keep the paper (`sec:cautionary`) and the code in sync.

### Verified facts (brute force, 3 colors) — the source of every range in the paper

| n range | reversal a symmetry? | strict `<_lex` augmented | non-strict `≤_lex` augmented |
|---------|----------------------|--------------------------|------------------------------|
| 1, 13   | yes (all palindromes)| **UNSAT → false cert.**  | SAT (all retained)           |
| 3–12    | **no**               | SAT (correct)            | SAT (correct)                |
| ≥14     | yes (vacuous, UNSAT) | UNSAT (correct)          | UNSAT (correct)              |

Consequences used below: the strict leader fabricates the false certificate
exactly at the all-palindrome sizes (`n = 1, 13`); the non-strict `≤_lex` never
produces a wrong answer on Schur (it is *accidentally* equisatisfiable at every
`n`), but it is still not a *provable* SBC for `3 ≤ n ≤ 12` because reversal is not
a symmetry there. The correct, sound use of a reversal leader in this repo is
**Langford** (`CSP/L2S/Proofs/LangfordSB.lean`), which uses a **non-strict**
single-variable leader `le_const 0 (n-1)` and has no palindrome solutions, so it
sidesteps this failure entirely.

## 2. The exact API to build on (verified against the current tree)

All of this is already in the repo; reuse it rather than redefining.

- `VarType n := Fin n` (`CSP/L2S/Core.lean:34`).
- `IntDomain := ℤ`, `IntAssignment n := VarType n → IntDomain`
  (`CSP/L2S/Core.lean:31,44`).
- `IntCSP` is `⟨num_vars, constraints⟩` (`CSP/L2S/Core.lean:286`).
- `isSolutionInt csp a := ∀ c ∈ csp.constraints, satisfiesConstraintInt c a`
  (`CSP/L2S/Core.lean:314`), and `satisfiesConstraintInt c a := patternHolds c a`.
- **Decidability is already available:** `patternHolds c a` has a `Decidable`
  instance (`CSP/L2S/Core.lean:263`, `cases c <;> ... <;> infer_instance`). Since
  `isSolutionInt` is a bounded `∀` over a concrete list, `isSolutionInt csp a` is
  decidable for any *concrete* `csp` and *concrete* `a`. This is what makes the
  witness steps dischargeable by `decide`.
- `VariableSymmetry csp β := ∀ a, isSolutionInt csp a → isSolutionInt csp (a ∘ β)`
  (`CSP/L2S/Symmetry.lean:42`). Note the composition is `a ∘ β`.

Schur CSP to use (domain `0 .. colors-1`, which matches the paper witness
`[0,1,1]`):

- `schurTriples n : List (Fin n × Fin n × Fin n)` (`CSP/L2S/Proofs/SchurEquivalence.lean:53`).
  It generates 0-indexed triples `(i, j, k)` with `k = i + j + 1`, `i ≤ j`, `k < n`.
  Check: `schurTriples 3 = [(0,0,1), (0,1,2)]` (labels `1+1=2` and `1+2=3`).
- `schur_csp_sb n colors (schurTriples n) : IntCSP` (`CSP/L2S/Proofs/SchurSB.lean:50`),
  which is `⟨n, schur_bound_constraints n colors ++ schur_triple_constraints n (schurTriples n)⟩`.
  Bounds are `bound v 0 (colors-1)`.

So the paper's stylized `schur 3 3` should be read as
`schur_csp_sb 3 3 (schurTriples 3)`.

The reversal permutation:

- `Fin.revPerm : Equiv.Perm (Fin n)` (`Mathlib/Data/Fin/Rev.lean:35`), the
  involution `i ↦ n-1-i`. Since `VarType n = Fin n`, this **is** the paper's
  `reversal n` (0-indexed form of `i ↦ n+1-i`). Import `Mathlib.Data.Fin.Rev`.

SBC API (needed for section 5, the "not an SBC" proof):

- `variableSymmetryBreakingConstraint csp c` (`CSP/L2S/Symmetry.lean:183`):
  `∀ a, isSolutionInt csp a → ∃ β, VariableSymmetry csp β ∧
   isSolutionInt (csp.addConstraint c) (a ∘ β)`. This is the obligation the
  framework demands to add `c` soundly.
- `csp.addConstraint c` (`CSP/L2S/Core.lean:354`): prepends `c` to the constraint
  list.
- `variableSymmetryBreaking_equisatisfiability` (`CSP/L2S/Symmetry.lean:256`):
  `variableSymmetryBreakingConstraint csp c → equisatisfiable csp (csp.addConstraint c)`.
  Its contrapositive is the cheap route in section 5: a proof that the augmented
  CSP is UNSAT while the base is SAT (i.e. `¬ equisatisfiable`) yields
  `¬ variableSymmetryBreakingConstraint`.
- The **strict lex leader is not yet encoded** as an `IntConstraint`. This is the
  one piece of new modelling the SBC refutation needs (see section 5). Langford's
  `le_const 0 (n-1)` (`CSP/L2S/Backends/PB/Bench/Generators.lean:213`) is the
  precedent for a *single-variable* leader, but the Schur example uses a full
  lexicographic comparison `x <_lex rev(x)`, which must be added to the library.

## 3. The n = 3 proof (the theorem in the paper)

Sanity check of the witness before writing any Lean:

- Witness `a := ![0,1,1] : Fin 3 → ℤ`. Bounds: all values in `0..2`, OK.
  Triple `(0,0,1)`: values `0,0,1` not all equal, OK. Triple `(0,1,2)`: values
  `0,1,1` not all equal, OK. So `a` is a solution.
- `Fin.revPerm` on `Fin 3`: `0 ↦ 2, 1 ↦ 1, 2 ↦ 0`. Then
  `(a ∘ revPerm) = ![a 2, a 1, a 0] = ![1,1,0]`.
- On `a ∘ revPerm`, triple `(0,0,1)` reads values `1,1,1`: all equal, so
  `schur_triple 0 0 1` is **violated**. Hence `a ∘ revPerm` is not a solution.

The negation of `VariableSymmetry` is `∃ a, isSolutionInt csp a ∧ ¬ isSolutionInt csp (a ∘ β)`.
Both halves are decidable for the concrete witness, so the proof is essentially:

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Symmetry
import CSP.L2S.Proofs.SchurEquivalence   -- for schurTriples
import CSP.L2S.Proofs.SchurSB            -- for schur_csp_sb
import Mathlib.Data.Fin.Rev

open CSP.L2S

/-- Witness solution of the 3-color Schur CSP at n = 3 whose reversal is not a
    solution: `[0,1,1]` reverses to `[1,1,0]`, monochromatic on `1 + 1 = 2`. -/
def schurReversalWitness : IntAssignment 3 := ![0, 1, 1]

theorem reversal_not_schur_symmetry :
    ¬ VariableSymmetry (schur_csp_sb 3 3 (schurTriples 3)) Fin.revPerm := by
  intro h
  -- `h` applied to the witness says its reversal is also a solution.
  have hbad := h schurReversalWitness (by decide)
  -- but the reversal violates the (0,0,1) triple:
  revert hbad
  decide
```

Notes for the implementer:

- The two `decide`s are the crux. They require `schur_csp_sb 3 3 (schurTriples 3)`
  and `schurReversalWitness ∘ Fin.revPerm` to reduce to closed terms. `schurTriples`,
  `schur_csp_sb`, and `Fin.revPerm` are all computable, so this should go through.
- If `decide` is too slow or gets stuck on `Fin.revPerm` reduction (the `Equiv`
  wrapper sometimes blocks `decide`'s whnf), try, in order:
  1. `simp only [Fin.revPerm, Equiv.coe_fn_mk, Function.comp]` to expose `Fin.rev`
     before `decide`;
  2. replace the second `decide` by an explicit contradiction: extract the
     `(0,0,1)` conjunct with `have := hbad (schur_triple 0 0 1) (by simp [...])`
     and close with `simp`/`decide` / `omega`;
  3. `native_decide` as a last resort (adds the compiler to the trusted base for
     this lemma; acceptable for a counterexample, but prefer `decide`).
- Do **not** state the witness as `fun i => [0,1,1].get i` or similar; use the
  `![...]` matrix notation so `decide` can compute `a ∘ Fin.revPerm` directly.

### Where to put it

`CSP/L2S/Proofs/` is the right home: it already holds every per-family
reformulation proof (`SchurSB.lean`, `SchurValuePrecedence.lean`,
`SchurEquivalence.lean`, `MutilatedSB.lean`, ...). Create
`CSP/L2S/Proofs/SchurReversalCounterexample.lean` and add it to the appropriate
import aggregator if the build uses one (check `CSP.lean` / `lakefile`). Keep the
theorem name `reversal_not_schur_symmetry` so it matches the `lstlisting` in
`sec:cautionary` verbatim.

## 4. Prove the negation across the whole satisfiable range (3 ≤ n ≤ 12)

The paper claims more than the `n = 3` case: with 3 colors the reversal is **not**
a symmetry for every `3 ≤ n ≤ 12`. Prove exactly this range. It is verified by
brute force (see below); do **not** widen it, because the statement is *false*
outside it:

- **`n = 1, 2`:** reversal is accidentally a genuine symmetry (`n = 2`: the only
  triple is `1+1=2`, and `not-all-equal(x₂,x₂,x₁)` is the same predicate as
  `not-all-equal(x₁,x₁,x₂)`), so `¬ VariableSymmetry` is false.
- **`n = 13`:** all `18` solutions are palindromes, so `s ∘ rev = s` for every
  solution and reversal maps each solution to *itself*. Reversal is a genuine
  symmetry here; `¬ VariableSymmetry` is false. (This is the same palindrome fact
  the paper uses to explain why the strict leader deletes every solution at
  `n = 13`. The collapse there is due to strictness, not a missing symmetry.)
- **`n ≥ 14` with 3 colors:** UNSAT (`S(3) = 13`), so `VariableSymmetry` holds
  vacuously; `¬ VariableSymmetry` is false.

So the honest theorem is bounded on both sides:

```lean
theorem reversal_not_schur_symmetry_range
    (n : ℕ) (hlo : 3 ≤ n) (hhi : n ≤ 12) :
    ¬ VariableSymmetry (schur_csp_sb n 3 (schurTriples n)) Fin.revPerm
```

**How to prove it.** Each `n` in the range is a separate concrete instance, so the
clean route is `interval_cases n` followed by the `n = 3` recipe of section 3 in
each of the 10 branches. `decide` cannot *find* the witness (the statement negates
a `∀` over ℤ-assignments), so each branch must supply its own witness explicitly,
then discharge both halves by `decide`. The witnesses below were found by brute
force; each is a solution of `schur_csp_sb n 3 (schurTriples n)` whose reversal
makes the diagonal triple `1+1=2` (or another triple) monochromatic:

| n  | witness assignment (0-indexed, values in {0,1,2}) |
|----|----------------------------------------------------|
|  3 | `[0,1,1]`                                           |
|  4 | `[0,1,0,2]`                                          |
|  5 | `[0,1,0,2,2]`                                        |
|  6 | `[0,1,0,2,0,1]`                                      |
|  7 | `[0,1,0,2,0,1,1]`                                    |
|  8 | `[0,1,0,2,0,2,0,1]`                                  |
|  9 | `[0,1,0,2,0,2,0,1,1]`                                |
| 10 | `[0,1,0,2,1,1,2,0,2,0]`                              |
| 11 | `[0,1,0,2,1,2,2,0,2,0,1]`                            |
| 12 | `[0,1,0,2,1,2,2,0,2,0,1,0]`                          |

Suggested structure: a witness lookup `schurRevWitness : (n : ℕ) → IntAssignment n`
defined by `match` on the 10 values (return `![...]`, default `![]`), and a single
proof that `interval_cases n <;> · (exact per-branch disproof using
`schurRevWitness n`)`. Keep the standalone `n = 3` theorem
`reversal_not_schur_symmetry` too, since the paper's `lstlisting` names it; it can
just be `reversal_not_schur_symmetry_range 3 (by decide) (by decide)`.

Same `decide` caveats as section 3 apply per branch (unfold `Fin.revPerm` via
`simp` first if `decide` stalls; `native_decide` only as a last resort).

### Optional: an unbounded "all n" theorem (more colors)

If you also want a genuinely unbounded result, keep the problem satisfiable by
letting the color count grow: for `3 ≤ n` and `c ≥ n-1`, reversal is not a
symmetry of `schur_csp_sb n c (schurTriples n)`. Uniform witness: color numbers
`n-1` and `n` (0-indexed `n-2`, `n-1`) the same and every other number distinctly.
It is sum-free (no triple fits in `{n-1,n}` since `(n-1)+(n-1) = 2n-2 > n`), yet
its reversal makes the diagonal triple `1+1=2` monochromatic. This one is a real
parametric proof (not `decide`): prove `a` is a solution by casing membership over
`schur_bound_constraints`/`schur_triple_constraints` with `omega` on the `Fin`
values, then contradict the symmetry hypothesis at `(0,0,1) ∈ schurTriples n`
using `Fin.rev` arithmetic. This is optional; the bounded range above is what the
paper text asserts.

## 5. Prove the strict leader is not a valid SBC (obligation 2, the real cause at n = 13)

Sections 3–4 refute obligation 1 (the symmetry). This section refutes obligation 2
(the SBC), which is what actually fabricates the false `S(3) < 13`. The target:

```lean
theorem schur_leader_not_sbc :
    ¬ variableSymmetryBreakingConstraint (schur_csp_sb 13 3 (schurTriples 13)) strictLexLeader
```

where `strictLexLeader : IntConstraint 13` encodes `x <_lex rev(x)`.

**Prerequisite (new modelling).** The strict lexicographic leader is not in the
constraint library yet. Add `strictLexLeader n : IntConstraint n` encoding
`x <_lex (x ∘ rev)`, i.e. there is a position `p` with `x p < x (rev p)` and
`x q = x (rev q)` for all `q < p`. This is the one nontrivial new definition; see
Langford's `le_const 0 (n-1)` for the (much simpler) single-variable precedent.

**Why the obligation fails at n = 13 (the argument to formalize).** Every solution
of `schur_csp_sb 13 3 _` is a palindrome (verified by brute force; 18 solutions,
all fixed by `rev`). The obligation asks: for every solution `s`, some symmetry
image `s ∘ β` (still a solution, since `β` is a symmetry) also satisfies the
leader. But any assignment `a` satisfying `x <_lex rev(x)` has `a ≠ a ∘ rev`,
whereas every solution here equals its own reversal. So no symmetry image of a
solution can satisfy the leader, and the obligation is false.

Two ways to formalize, in increasing faithfulness / cost:

- **(a) Recommended — via equisatisfiability (cheap, reuses the pipeline).** Prove
  `¬ equisatisfiable (schur_csp_sb 13 3 _) ((schur_csp_sb 13 3 _).addConstraint (strictLexLeader 13))`,
  then apply `mt variableSymmetryBreaking_equisatisfiability` to obtain
  `schur_leader_not_sbc`. The `¬ equisatisfiable` has two halves:
    1. base is SAT: exhibit one palindrome solution (e.g. an `S(3)=13` colouring)
       and close by `decide`;
    2. augmented is UNSAT: this is exactly the paper's false certificate. Discharge
       it through the existing PB/VeriPB backend (the same path used for genuine
       UNSAT results), or by `native_decide` if the instance is small enough.
  This route says, precisely, that *the false certificate is itself the disproof of
  soundness*, which is the paper's point.

- **(b) Direct — unfold the obligation.** Provide a palindrome solution `s`, then
  show `∀ β, VariableSymmetry csp β → ¬ isSolutionInt (csp.addConstraint (strictLexLeader 13)) (s ∘ β)`.
  Needs two lemmas: (i) `satisfiesConstraintInt (strictLexLeader n) a → a ≠ a ∘ Fin.revPerm`
  (a strict lex leader is falsified by any palindrome — pure lex reasoning, no
  search); and (ii) every solution of `schur_csp_sb 13 3 _` is a palindrome
  (`native_decide` over `{0,1,2}^13`, ~1.6M assignments; heavier). Then `s ∘ β` is
  a solution, hence a palindrome, hence fails the leader.

Route (a) is preferred: it avoids the `3^13` enumeration and ties directly to the
certified UNSAT machinery.

**Contrast to bank against (documents the strict-vs-non-strict finding).** With the
**non-strict** leader `≤_lex`, obligation 2 *holds* at n = 13, trivially: every
solution is a palindrome, so `s ≤_lex rev(s) = s ≤_lex s` is true, and `β = identity`
(always a `VariableSymmetry`, `Symmetry.lean:99`) discharges the obligation for every
solution. So `variableSymmetryBreakingConstraint (schur 13 3) (≤_lex)` is provable,
but *vacuous* (it removes nothing: all 18 solutions are retained). This mirrors
Langford, where the non-strict leader is sound; the difference is that on Schur the
non-strict leader is still not provable for `3 ≤ n ≤ 12` (obligation 1 fails there),
whereas Langford's reversal genuinely is a symmetry. A one-line `decide`/`native_decide`
lemma proving the `≤_lex` SBC at n = 13 is a nice optional companion that makes the
strict-vs-non-strict distinction concrete in the repo.

## 6. Checklist

- [ ] Create `CSP/L2S/Proofs/SchurReversalCounterexample.lean`.
- [ ] **Obligation 1:** prove `reversal_not_schur_symmetry_range` (3 ≤ n ≤ 12) via
      section 4, and derive `reversal_not_schur_symmetry` (n = 3) from it so the
      paper's `lstlisting` name resolves.
- [ ] **Obligation 2:** encode `strictLexLeader n` and prove `schur_leader_not_sbc`
      via section 5 route (a) (`¬ equisatisfiable` + `mt variableSymmetryBreaking_equisatisfiability`).
- [ ] (Optional) prove the `≤_lex` SBC holds vacuously at n = 13, to bank the
      strict-vs-non-strict contrast.
- [ ] `lake build` the file (do not use `native_decide` unless `decide` fails).
- [ ] `#print axioms` on both main theorems: expect only standard axioms if
      `decide` was used (the `native_decide`/PB path will pull in the reflection
      axiom, which is acceptable and expected for the augmented-UNSAT step).
- [ ] Wire the file into whatever import root the build expects.
- [ ] (Optional) Prove the unbounded `c ≥ n-1` non-symmetry version (section 4).
- [ ] Keep names, the `3 ≤ n ≤ 12` range, and the two-obligation framing in sync
      with `sec:cautionary` in `paper.tex`.
