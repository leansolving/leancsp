import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Ancient China Map Coloring

Color 14 Chinese provinces with 4 colors so adjacent provinces differ.
-/

def bound_constraints (nodes : ℕ) (colors : ℕ) : List (TaggedConstraint nodes) :=
  (List.finRange nodes).map (fun v => bound v 1 colors)

def edge_constraints (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) : List (TaggedConstraint nodes) :=
  edges.map (fun (u,v) => not_equal u v)

def graph_coloring_csp (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : HomogeneousCSP :=
  ⟨ nodes ,
    bound_constraints nodes colors ++ edge_constraints nodes edges ⟩


def graph : HomogeneousCSP :=
  let nodes := 14
  -- 0=Si, 1=Yan, 2=Yu, 3=Xu, 4=Qing, 5=Ji, 6=You, 7=Bing, 8=Yong, 9=Liang, 10=Yi, 11=Jing, 12=Yang, 13=Jiao
  let edges := [
    (9,8), (8,10), (8,11), (8,0), (10,11), (10,13), (13,11), (13,12), (11,12), (11,8),
    (11,0), (11,2), (12,2), (12,3), (2,0), (2,1), (2,3), (3,1), (3,4), (1,0),
    (1,5), (1,5), (1,4), (4,5), (5,6), (5,7), (5,0), (6,7), (7,0)
  ]
  let colors := 4
  graph_coloring_csp nodes edges colors

def main : IO Unit := do
  saveAllBackendsAutoTimed graph
