# Guide for proving Symmetry Breaking Constraints Correctness

For proving that an added constraint to a CSP is a valid symmetry breaking constraints, we will need the following:

## Necessary definitions

Before starting with the proofs, there must be defined:

1. The **Constraint Satisfaction Problem** (`csp`): with type `IntCSP`, containts the constraints of the original problem.
2. The candidate to **Symmetry-Breaking Constraint** (`sbc`): with type `IntConstraint <num_vars>`.
3. The **Symmetry Function** ($\delta$/$\beta$): with type `Equiv.Perm IntDomain` or `Equiv.Perm (VarType <num_vars>)`.

## Results to be proven

1. **Symmetry Function Correctness**: prove `DomainSymmetry csp \delta` (resp. `VariableSymmetry csp \beta`). It is necessary to show that the symmetry function preserves solutions of the original CSP, i.e., preserves all the constraints. In this prove, we may distiguish between bound constraints and the remaining constraints of the problem, and reuse the bound constraint preservation results under symmetries included in `Symmetry.lean`.

2. **Variable (or Domain) Symmetry Breaking Constraint Correctness**: prove `variableSymmetryBreakingConstraint csp sbc` (resp. domain). It is necessary to show that, for every solution of the original csp, there exists a symmetry function such that the solution composed with the symmetry is a solution of the extended CSP, including the candidate to symmetry breaking constraint. The idea of the proof is the following:
    - `intro sol h_sol`
    - Case distinction:
        - If `sol` is a solution of the extended csp, then use the identity symmetry (trivial case)
        - If not, use the defined symmetry.
            - Have `Variable(Domain)Symmetry` using result 1.
            - Have `isSolution extended_csp (sol \comp \beta)` (resp. `\delta`):
                - For original constraints, use the fact that the symmetry function is correct (preserves all solutions)
                - For the new constraint, prove that the composed assignment satisfies it.

3. **Symmetry Breaking Constraint Correctness**: have `SymmetryBreakingConstraint csp sbc` using 2.

4. **Equisatisfiability**: have `equisatisfiable csp extended_csp` applying the `symmetryBreaking_equisatisfiability` result from `Symmetry.lean` and the previous results.

## Working with the pattern-based satisfaction semantics

Constraint satisfaction is `IntCSP.satisfiesConstraintInt c a := patternHolds c a`
(`Core.lean`), a direct proposition per constraint pattern. Per-constraint
reasoning goes through the two-way bridges in `PatternBridges.lean`
(`bound_holds_iff`, `not_equal_holds_iff`, `alldifferent_holds_iff`, …), e.g.

```lean
rw [← IntCSP.satisfiesConstraintInt_iff_toDynamic] at h_sat ⊢   -- only for taggedConstraint*Symmetric
rw [not_equal_holds_iff] at h_sat ⊢
```

When a bridge fails to match (typically inside `*SymmetryBreakingConstraint`
proofs, where the implicit `num_vars` is an unreduced `(csp.addConstraint sbc).num_vars`
projection over a `Fin` literal), unfold directly instead — put the CSP
definition in the simp set so the `valAt` dite discharges:

```lean
simp only [IntCSP.satisfiesConstraintInt, sb_constraint, less_than_const, patternHolds,
  valAt, IntCSP.addConstraint, nqueens_csp, h_n, dif_pos, Function.comp_apply]
```
