import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Strange graph numbering

Label the 8 vertices `a..h` (variables `x0..x7`) of a fixed 17-edge graph with the
integers `1..8`, each used once (`alldifferent`), so that adjacent labels differ by
at least 2 in absolute value.

```
  b-e
 /|*|\
a-c-f-h
 \|*|/
  d-g
```
-/

-- Create bound constraints for n variables with domain 1..n
def graph_bounds (n : ℕ) : List (IntConstraint n) :=
  List.finRange n |>.map (fun i => bound i 1 n)

-- Define graph edges as pairs of vertex indices
def graph_edges : List (ℕ × ℕ) :=
  [ (0, 1),   -- a-b
    (0, 2),   -- a-c
    (0, 3),   -- a-d
    (1, 2),   -- b-c
    (1, 4),   -- b-e
    (1, 5),   -- b-f
    (2, 3),   -- c-d
    (2, 4),   -- c-e
    (2, 5),   -- c-f
    (2, 6),   -- c-g
    (3, 5),   -- d-f
    (3, 6),   -- d-g
    (4, 5),   -- e-f
    (4, 7),   -- e-h
    (5, 6),   -- f-g
    (5, 7),   -- f-h
    (6, 7)    -- g-h
  ]


-- Helper to create abs_diff_ge constraints for all edges
def make_graph_constraints (n : ℕ) (edges : List (ℕ × ℕ)) (min_diff : ℤ) :
    List (IntConstraint n) :=
  edges.filterMap fun (u, v) =>
    if h1 : u < n then
      if h2 : v < n then
        some (CSP.L2S.abs_diff_ge ⟨u, h1⟩ ⟨v, h2⟩ min_diff)
      else none
    else none

-- Create alldifferent constraint for all n variables
def graph_alldifferent (n : ℕ) : IntConstraint n :=
  alldifferent (_root_.Vector.ofFn id)

-- Complete graph numbering CSP
def graph_numbering : IntCSP :=
  let n := 8
  let min_diff := 2
  ⟨n,
   graph_bounds n ++
   [graph_alldifferent n] ++
   make_graph_constraints n graph_edges min_diff⟩
