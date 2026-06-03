import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Ramsey Number R(3,3)

## Problem Description
R(3,3) = 6: every 2-colouring of the edges of K₆ contains a monochromatic
triangle, while K₅ admits a colouring with none (the two 5-cycles).

## CSP Formulation
- **Variables**: one per edge of Kₙ (edges {i,j}, i<j, indexed lexicographically).
- **Domain**: {0,1} (the two edge colours).
- **Constraint**: for each triangle {i,j,k} (i<j<k), its three edge colours are
  **not all equal** — the `schur_triple` pattern over the edges {i,j}, {i,k}, {j,k}.

## Instances
- `ramsey_3_3_K5` : K₅ — **SAT** (5-cycle witness).
- `ramsey_3_3_K6` : K₆ — **UNSAT** (this is R(3,3) = 6).

## Showcase
PBLean / veripb benchmark `ramsey6` (the R(3,3) upper-bound certificate).

## Constraint families
`bound`, `schur_triple` (3-ary not-all-equal).
-/

-- Number of edges in Kₙ.
def ramsey_num_edges (n : ℕ) : ℕ := n * (n - 1) / 2

-- Index of edge {i,j} (i<j) in Kₙ, lexicographic over (i,j):
-- (edges with smaller first endpoint) + (offset within first endpoint).
def ramsey_edge_index (n i j : ℕ) : ℕ :=
  i * (n - 1) - i * (i - 1) / 2 + (j - i - 1)

-- Each edge variable is Boolean (domain {0,1}).
def ramsey_bounds (n : ℕ) : List (TaggedConstraint (ramsey_num_edges n)) :=
  List.finRange (ramsey_num_edges n) |>.map (fun e => bound e 0 1)

-- All triangles {i,j,k} (i<j<k) as triples of edge-variable indices.
def ramsey_triangles (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun i =>
    (List.range n).flatMap fun j =>
      (List.range n).filterMap fun k =>
        if i < j ∧ j < k then
          some (ramsey_edge_index n i j, ramsey_edge_index n i k, ramsey_edge_index n j k)
        else none

-- "No monochromatic triangle" = not-all-equal over each triangle's three edges.
def ramsey_constraints (n : ℕ) : List (TaggedConstraint (ramsey_num_edges n)) :=
  let m := ramsey_num_edges n
  (ramsey_triangles n).filterMap fun (e1, e2, e3) =>
    if h1 : e1 < m then
      if h2 : e2 < m then
        if h3 : e3 < m then
          some (schur_triple ⟨e1, h1⟩ ⟨e2, h2⟩ ⟨e3, h3⟩)
        else none
      else none
    else none

def ramsey_r33_csp (n : ℕ) : HomogeneousCSP :=
  ⟨ramsey_num_edges n, ramsey_bounds n ++ ramsey_constraints n⟩

-- K₅ is 2-colourable with no monochromatic triangle (SAT).
def ramsey_3_3_K5 : HomogeneousCSP := ramsey_r33_csp 5

-- R(3,3) = 6: K₆ forces a monochromatic triangle (UNSAT).
def ramsey_3_3_K6 : HomogeneousCSP := ramsey_r33_csp 6

def main : IO Unit := do
  saveAllBackendsAutoTimed ramsey_3_3_K6
