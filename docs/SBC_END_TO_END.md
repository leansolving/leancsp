# End-to-end UNSAT via symmetry breaking

This document describes the **end-to-end workflow** that unifies the project's two halves:

1. the **symmetry-breaking correctness** proofs (`CSP/L2S/Proofs/*SB.lean`), and
2. the **verified pseudo-Boolean UNSAT-certificate** backend (`CSP/L2S/Backends/PB/`),

to produce a kernel-checked `¬ csp.isSatisfiableInt` for an **original** CSP, obtained by proving a
symmetry-breaking constraint correct, certifying the *extended* CSP UNSAT with an external PB solver,
and composing the two in Lean.

## The pattern

For a CSP `csp` and a constraint `c`:

```
csp                       ──[ *SB.lean ]────────▶  symmetryBreakingConstraint csp c
csp.addConstraint c       ──[ RoundingSat/VeriPB, csp_unsat_file ]──▶  ¬ (csp.addConstraint c).isSatisfiableInt
                          ──[ CSP.L2S.unsat_of_sbc ]────────────────▶  ¬ csp.isSatisfiableInt
```

The bridge is one theorem (`CSP/L2S/Symmetry.lean`), verified against the live project:

```lean
theorem unsat_of_sbc (csp : IntCSP) (c : IntConstraint csp.num_vars)
    (h_sbc   : symmetryBreakingConstraint csp c)
    (h_unsat : ¬ isSatisfiableInt (csp.addConstraint c)) :
    ¬ isSatisfiableInt csp :=
  fun hs => h_unsat ((symmetryBreaking_equisatisfiability csp c h_sbc).mp hs)
```

(`unsat_of_domain_sbc` / `unsat_of_variable_sbc` are the specialised forms.)

It composes the existing `symmetryBreaking_equisatisfiability` (the SBC preserves satisfiability) with
the certificate's `¬ (csp.addConstraint c).isSatisfiableInt`. Every end-to-end theorem below is
**axiom-clean**: `propext, Classical.choice, Quot.sound`, plus the one `native_decide` axiom carrying
the kernel-checked PB certificate — no `sorryAx`, no new axioms.

## Layout

| Layer | Location |
|-------|----------|
| Bridge + SBC theory | `CSP/L2S/Symmetry.lean` (`unsat_of_sbc`, `*SymmetryBreaking*`) |
| SBC correctness proofs | `CSP/L2S/Proofs/<Family>SB.lean` |
| Extended-CSP certs | `CSP/L2S/Backends/PB/Problems/<Family>SBC.lean` + `certs/<name>_sbc.pbp` |
| End-to-end theorems | `CSP/L2S/EndToEnd/<Family>.lean` |

Each `EndToEnd/<Family>.lean` is built individually by a bare `lake build` (the lakefile glob
`.andSubmodules CSP` covers the `EndToEnd/` subtree). They are **not** aggregated into one import,
because two of the reused proof files (`GraphColoringSB`, `NQueensSB`) define clashing root-namespace
helpers (`bound_constraints`, `sb_constraint`) and cannot share one environment — a pre-existing wart
to clean up when those files are namespaced.

## Delivered end-to-end theorems

| Theorem (`CSP.L2S.EndToEnd.…`) | Original CSP | SBC used | Symmetry broken | Cert |
|---|---|---|---|---|
| `Schur.schur_2_5_unsat` | `Schur.schur_sb 5 2` — `{1..5}` 2-coloured sum-free | `x₀ = 0` (`equals_const`) | colour swap `S₂` | `schur_2_5_sbc.pbp` |
| `Schur.schur_3_14_unsat` | `Schur.schur_sb 14 3` — `{1..14}` 3-coloured sum-free | `x₀ = 0` | colour swap `S₃` | `schur_3_14_sbc.pbp` |
| `GraphColoring.k3_2col_unsat` | `graph_coloring_csp 3 K₃ 2` | `x₀ = 0` | colour swap `S₂` | `k3_sbc.pbp` |
| `GraphColoring.k4_3col_unsat` | `graph_coloring_csp 4 K₄ 3` | `x₀ = 0` | colour swap `S₃` | `k4_sbc.pbp` |
| `NQueens.nqueens_2_unsat` | `nqueens_csp 2` | `x₀ < (n+1)/2` (`less_than_const`) | horizontal reflection | `nqueens_2_sbc.pbp` |
| `NQueens.nqueens_3_unsat` | `nqueens_csp 3` | `x₀ < (n+1)/2` | horizontal reflection | `nqueens_3_sbc.pbp` |
| `OddCycle.c5_2col_unsat` | `graph_coloring_csp 5 C₅ 2` | `x₀ = 0` | colour swap `S₂` | `c5_sbc.pbp` |
| `OddCycle.c7_2col_unsat` | `graph_coloring_csp 7 C₇ 2` | `x₀ = 0` | colour swap `S₂` | `c7_sbc.pbp` |
| `OddCycle.c9_2col_unsat` | `graph_coloring_csp 9 C₉ 2` | `x₀ = 0` | colour swap `S₂` | `c9_sbc.pbp` |

Each reuses an *already-proved* SBC: `Schur.schur_sb_is_symmetry_breaking`,
`sb_constraint_is_symmetry_breaking` (graph colouring and N-Queens). The mathematical reading: the
Schur rows certify the Schur-number bounds `S(2) < 5` and `S(3) < 14`; the colouring rows certify that
`Kₙ` needs `n` colours; the N-Queens rows that 2- and 3-Queens are unsolvable.

## Why this matters for cutting-planes solving

The backend solves with **RoundingSat (cutting planes)**. The *value* of symmetry breaking is largest on
**colour-symmetric** families (Schur, Van der Waerden, Ramsey, graph colouring), where the colour group
`S_k` creates many symmetric branches; it is smallest on pigeonhole / mutilated-chessboard, which already
have short cutting-planes proofs (those are *correctness/breadth* demonstrators, not speedup ones). See
the per-family expectation in the roadmap; the quantitative comparison is the scaling experiment below.

## Roadmap (next steps)

The pattern above is established and template-complete. Remaining work, in priority order:

1. **Value precedence** (general SBC, `CSP/L2S/Symmetry.lean`). The reused SBCs fix `x₀ = 0`, one
   generator of `S_k` (orbit shrink ×`k`). *Value precedence* — "colour `v` first appears only after
   `v-1`" — breaks the full `S_k` (orbit → 1, shrink up to `k!`). Search-free correctness proof
   (relabel colours by first occurrence); the one non-routine step is the Mathlib lemma
   "injective partial map on a `Fintype` extends to a permutation". One lemma upgrades every
   colour-symmetric family and enables the **none / one-swap / value-precedence** granularity
   comparison.
2. **Schur first-occurrence hierarchy** (capstone): prove `pⱼ ≤ S(j)+1` (the prefix before colour `j`
   is a `j`-colour sum-free colouring), a self-strengthening SBC that *consumes* the kernel-checked
   smaller-Schur theorem (Heule's *Schur Number Five* technique).
3. **New SBC proofs**: `VanDerWaerdenSB` (colour precedence + reflection `i ↦ n+1-i`), `RamseySB`
   (2-colour precedence; vertex matrix-lex as stretch), `PigeonholeSB` (pigeon `S_{n+1}` lex + hole
   value precedence), `OddCycleSB`, `MutilatedChessboardSB`, board `D₄` SBCs — each with its
   extended cert(s) and `EndToEnd/` module.
4. **`SchurNoIndexSymmetry`** (cheap negative lemma): any `π` on `{1..n}` preserving `a+b=c` is `id`,
   so colour precedence is the *only* Schur SBC.
5. **Scaling experiment** (`scripts/scaling/`, `docs/SCALING.md`): per family size-sequence, log
   RoundingSat wall-time and proof size in the three SBC regimes; emit CSV + plot.

## Regenerating a cert

```bash
scripts/gen_cert.sh <Module> "<extended cspExpr>" <out>_sbc
# e.g.
scripts/gen_cert.sh CSP.L2S.Proofs.SchurSB "Schur.extended_schur 5 (by decide) 2" schur_2_5_sbc
```

prints `numVars` (pass to `csp_unsat_file`) and commits `Problems/certs/<out>_sbc.pbp`. Re-checking a
committed theorem needs only Lean + the Mathlib cache (RoundingSat/veripb not required).
