import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S
open CSP.L2S.IntCSP   -- for `listToFinVector`

/-!
# Paley Graph Independent Sets

## Problem Description
For a prime p ≡ 1 (mod 4) the Paley graph has vertex set ℤ/pℤ with an edge
{u,v} whenever u−v is a nonzero quadratic residue mod p. Its independence
number α is small; asserting an independent set of size α+1 is unsatisfiable.
For p = 13, α(Paley(13)) = 3, so an independent set of size 4 is impossible.

## CSP Formulation
- **Variables**: one per vertex 0..p−1, domain {0,1} (in the set or not).
- **Edge constraint**: for every edge {u,v}, at most one endpoint is selected
  (`at_most_k [u,v] 1`, i.e. x_u + x_v ≤ 1).
- **Size constraint**: `at_least_k` over all vertices with target = α+1.

The conjunction is UNSAT exactly when no independent set of size `target` exists,
certifying the independence-number upper bound — veripb's `Paley_p` benchmarks.

## Instances
- `paley_13_4` : Paley(13), target 4 — **UNSAT** (α = 3).

## Constraint families
`bound`, `at_most_k`, `at_least_k` (cardinality).
-/

-- Quadratic residues mod p (squares of 0..p−1; duplicates are harmless for `∈`).
def paley_residues (p : ℕ) : List ℕ :=
  (List.range p).map (fun x => (x * x) % p)

-- Each vertex is in or out of the independent set.
def paley_bounds (p : ℕ) : List (IntConstraint p) :=
  List.finRange p |>.map (fun i => bound i 0 1)

-- For every edge {u,v} (u<v, u−v a quadratic residue): x_u + x_v ≤ 1.
def paley_edge_constraints (p : ℕ) : List (IntConstraint p) :=
  (List.range p).flatMap fun u =>
    (List.range p).filterMap fun v =>
      if u < v ∧ ((v - u) % p) ∈ paley_residues p then
        match listToFinVector [u, v] p with
        | some ⟨_, sc⟩ => some (at_most_k sc 1)
        | none => none
      else none

-- Assert an independent set of size ≥ target over all vertices.
def paley_at_least (p target : ℕ) : List (IntConstraint p) :=
  match listToFinVector (List.range p) p with
  | some ⟨_, sc⟩ => [at_least_k sc target]
  | none => []

def paley_csp (p target : ℕ) : IntCSP :=
  ⟨p, paley_bounds p ++ paley_edge_constraints p ++ paley_at_least p target⟩

-- Paley(13): independence number is 3, so a size-4 independent set is UNSAT.
def paley_13_4 : IntCSP := paley_csp 13 4
