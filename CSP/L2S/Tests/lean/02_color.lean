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

def bound_constraints (nodes : ℕ) (colors : ℕ) : List (IntConstraint nodes) :=
  (List.finRange nodes).map (fun v => bound v 1 colors)

def edge_constraints (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) : List (IntConstraint nodes) :=
  edges.map (fun (u,v) => not_equal u v)

def graph_coloring_csp (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : IntCSP :=
  ⟨ nodes ,
    bound_constraints nodes colors ++ edge_constraints nodes edges ⟩


def graph : IntCSP :=
  let nodes := 14
  -- 0=Si, 1=Yan, 2=Yu, 3=Xu, 4=Qing, 5=Ji, 6=You, 7=Bing, 8=Yong, 9=Liang, 10=Yi, 11=Jing, 12=Yang, 13=Jiao
  let edges := [
    (9,8), (8,10), (8,11), (8,0), (10,11), (10,13), (13,11), (13,12), (11,12), (11,8),
    (11,0), (11,2), (12,2), (12,3), (2,0), (2,1), (2,3), (3,1), (3,4), (1,0),
    (1,5), (1,5), (1,4), (4,5), (5,6), (5,7), (5,0), (6,7), (7,0)
  ]
  let colors := 4
  graph_coloring_csp nodes edges colors

/-- The triangle K₃ — the smallest non-2-colourable graph (odd cycle C₃). -/
def k3Edges : List (Fin 3 × Fin 3) := [(0, 1), (1, 2), (0, 2)]

/-- Colour K₃ with two colours: unsatisfiable (a triangle needs three colours).
    Drives the verified PB UNSAT proof `k3_2col_unsat`. -/
def k3_2col : IntCSP := graph_coloring_csp 3 k3Edges 2

/-- The complete graph K₄ (all six edges). -/
def k4Edges : List (Fin 4 × Fin 4) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Colour K₄ with three colours: unsatisfiable (χ(K₄) = 4).  Drives `k4_3col_unsat`,
    which exercises `encodeAllDifferent` on the multi-valued domain {1,2,3}. -/
def k4_3col : IntCSP := graph_coloring_csp 4 k4Edges 3

/-- The single edge K₂ (vertices 0–1). -/
def k2Edges : List (Fin 2 × Fin 2) := [(0, 1)]

/-- Colour 1 forbidden at both endpoints (a `not_equals_const` per vertex). -/
def k2Forbidden : List (Fin 2 × ℤ) := [(0, 1), (1, 1)]

/-- Colour the edge K₂ with two colours, but forbid colour 1 at both endpoints.
    This forces both vertices to colour 2, contradicting the edge — unsatisfiable.
    Drives `k2_forbidden_unsat`, the first end-to-end consumer of `encodeNeConst`
    (the verified `xⱼ ≠ const` encoder), alongside `not_equal`. -/
def k2_forbidden : IntCSP :=
  ⟨2, bound_constraints 2 2 ++ edge_constraints 2 k2Edges
        ++ k2Forbidden.map (fun p => not_equals_const p.1 p.2)⟩

/-! ## Odd cycles `C_n` (n odd) — the scaling family for 2-colourability

The odd cycle `C_n` on vertices `0..n-1` (edges `(i, i+1)`, closing `(n-1, 0)`) is
not 2-colourable for odd `n`.  These scale `k3_2col` (`C_3`, the triangle) and drive
the verified PB UNSAT proofs `c5_2col_unsat` / `c7_2col_unsat` / `c9_2col_unsat`
(`Backends/PB/OddCycle.lean`), the easy non-separation baseline of the scaling study
(`docs/SCALING.md`): all 0/1 coefficients, so both the cutting-planes certificate
and the resolution proof grow linearly. -/

/-- The cycle `C_5` (a pentagon): edges `(0,1),(1,2),(2,3),(3,4),(4,0)`. -/
def c5Edges : List (Fin 5 × Fin 5) := [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

/-- Colour the odd cycle `C_5` with two colours: unsatisfiable (odd cycles need three). -/
def c5_2col : IntCSP := graph_coloring_csp 5 c5Edges 2

/-- The cycle `C_7`: edges `(0,1),…,(5,6),(6,0)`. -/
def c7Edges : List (Fin 7 × Fin 7) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 0)]

/-- Colour the odd cycle `C_7` with two colours: unsatisfiable. -/
def c7_2col : IntCSP := graph_coloring_csp 7 c7Edges 2

/-- The cycle `C_9`: edges `(0,1),…,(7,8),(8,0)`. -/
def c9Edges : List (Fin 9 × Fin 9) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 0)]

/-- Colour the odd cycle `C_9` with two colours: unsatisfiable. -/
def c9_2col : IntCSP := graph_coloring_csp 9 c9Edges 2

def main : IO Unit := do
  saveAllBackendsAutoTimed graph
