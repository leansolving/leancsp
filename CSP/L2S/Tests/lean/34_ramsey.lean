import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

/-!
# Ramsey number R(3,3)

`R(3,3) = 6`: every 2-colouring of `K₆`'s edges contains a monochromatic triangle,
while `K₅` admits one with none (the two 5-cycles).

One variable per edge `{i,j}` (`i < j`, lexicographic) over `{0,1}`, with a
`schur_triple` not-all-equal constraint on each triangle's three edges.

Instances: `ramsey_3_3_K5` is SAT, `ramsey_3_3_K6` is UNSAT.
-/

-- Number of edges in Kₙ.
def ramsey_num_edges (n : ℕ) : ℕ := n * (n - 1) / 2

-- Index of edge {i,j} (i<j) in Kₙ, lexicographic over (i,j):
-- (edges with smaller first endpoint) + (offset within first endpoint).
def ramsey_edge_index (n i j : ℕ) : ℕ :=
  i * (n - 1) - i * (i - 1) / 2 + (j - i - 1)

-- Each edge variable is Boolean (domain {0,1}).
def ramsey_bounds (n : ℕ) : List (IntConstraint (ramsey_num_edges n)) :=
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
def ramsey_constraints (n : ℕ) : List (IntConstraint (ramsey_num_edges n)) :=
  let m := ramsey_num_edges n
  (ramsey_triangles n).filterMap fun (e1, e2, e3) =>
    if h1 : e1 < m then
      if h2 : e2 < m then
        if h3 : e3 < m then
          some (schur_triple ⟨e1, h1⟩ ⟨e2, h2⟩ ⟨e3, h3⟩)
        else none
      else none
    else none

def ramsey_r33_csp (n : ℕ) : IntCSP :=
  ⟨ramsey_num_edges n, ramsey_bounds n ++ ramsey_constraints n⟩

-- K₅ is 2-colourable with no monochromatic triangle (SAT).
def ramsey_3_3_K5 : IntCSP := ramsey_r33_csp 5

-- R(3,3) = 6: K₆ forces a monochromatic triangle (UNSAT).
def ramsey_3_3_K6 : IntCSP := ramsey_r33_csp 6
