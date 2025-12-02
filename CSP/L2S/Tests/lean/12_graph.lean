import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Strange Graph Numbering Problem

## Problem Description
Label the vertices of a specific graph with integers 1..8 such that:
1. Each number is used exactly once (alldifferent)
2. Adjacent vertices differ by at least 2 in absolute value

## Graph Structure
```
  b-e
 /|*|\
a-c-f-h
 \|*|/
  d-g
```

Where vertices are labeled a through h (8 vertices total).

## CSP Formulation
- **Variables**: 8 vertices (a, b, c, d, e, f, g, h) mapped to indices 0..7
- **Domain**: Each variable ranges from 1..8
- **Constraint 1**: All different (each number 1..8 used exactly once)
- **Constraint 2**: For each edge (u,v): |u - v| >= 2

## Vertex Mapping
- a = x0, b = x1, c = x2, d = x3
- e = x4, f = x5, g = x6, h = x7

## Graph Edges (17 edges)
From visualization:
- a(0) connects to: b(1), c(2), d(3)
- b(1) connects to: a(0), c(2), e(4), f(5)
- c(2) connects to: a(0), b(1), d(3), e(4), f(5), g(6)
- d(3) connects to: a(0), c(2), f(5), g(6)
- e(4) connects to: b(1), c(2), f(5), h(7)
- f(5) connects to: b(1), c(2), d(3), e(4), g(6), h(7)
- g(6) connects to: c(2), d(3), f(5), h(7)
- h(7) connects to: e(4), f(5), g(6)

## Source
MiniZinc examples - graph.mzn
-/

-- Create bound constraints for n variables with domain 1..n
def graph_bounds (n : ℕ) : List (TaggedConstraint n) :=
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
    List (TaggedConstraint n) :=
  edges.filterMap fun (u, v) =>
    if h1 : u < n then
      if h2 : v < n then
        some (CSP.L2S.abs_diff_ge ⟨u, h1⟩ ⟨v, h2⟩ min_diff)
      else none
    else none

-- Create alldifferent constraint for all n variables
def graph_alldifferent (n : ℕ) : TaggedConstraint n :=
  alldifferent (_root_.Vector.ofFn id)

-- Complete graph numbering CSP
def graph_numbering : HomogeneousCSP :=
  let n := 8
  let min_diff := 2
  ⟨n,
   graph_bounds n ++
   [graph_alldifferent n] ++
   make_graph_constraints n graph_edges min_diff⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed graph_numbering
