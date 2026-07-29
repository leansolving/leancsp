import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S
open CSP.L2S.IntCSP   -- for `listToFinVector`

/-!
# Paley graph independent sets

For a prime `p ≡ 1 (mod 4)` the Paley graph has vertex set `ℤ/pℤ` and an edge
`{u,v}` whenever `u − v` is a nonzero quadratic residue.  Asserting an independent
set of size `α + 1` is unsatisfiable, which certifies the independence number.

One `{0,1}` variable per vertex, `at_most_k [u,v] 1` per edge, and one `at_least_k`
over all vertices with target `α + 1`.

Instance: `paley_13_4` — Paley(13) with target 4, UNSAT since `α = 3`.
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
