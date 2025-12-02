import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Australia Map Coloring

Classic graph coloring: color 7 Australian regions with 4 colors so adjacent regions differ.
-/

def bound_constraints (nodes : ℕ) (colors : ℕ) : List (TaggedConstraint nodes) :=
  (List.finRange nodes).map (fun v => bound v 1 colors)

def edge_constraints (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) : List (TaggedConstraint nodes) :=
  edges.map (fun (u,v) => not_equal u v)

def graph_coloring_csp (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : HomogeneousCSP :=
  ⟨ nodes ,
    bound_constraints nodes colors ++ edge_constraints nodes edges ⟩


def australia : HomogeneousCSP :=
  let nodes := 7
  let edges := [
    (0,1),  -- wa != nt
    (0,2),  -- wa != sa
    (1,2),  -- nt != sa
    (1,3),  -- nt != q
    (2,3),  -- sa != q
    (2,4),  -- sa != nsw
    (2,5),  -- sa != v
    (3,4),  -- q != nsw
    (4,5)   -- nsw != v
  ]
  let colors := 4
  graph_coloring_csp nodes edges colors

def main : IO Unit := do
  saveAllBackendsAutoTimed australia
