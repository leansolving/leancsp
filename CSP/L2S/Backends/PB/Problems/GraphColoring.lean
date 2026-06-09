import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«02_color»

namespace CSP.L2S.PB.GraphColoring

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for graph colouring

`k3_2col` colours the triangle **K₃** with two colours (the smallest
non-2-colourable graph) and `k4_3col` colours **K₄** with three colours; both
(`Tests/lean/02_color.lean`) give each vertex a colour variable over `{1,…,c}`
with a `not_equal u v` per edge, and both are unsatisfiable (a `c`-clique needs
`c+1` colours).

Each is discharged by a **single** `csp_unsat` application over its committed
kernel certificate — no per-problem signature, encoding, or bridge.  The generic
encoder turns every `not_equal` edge into the aux-free order encoding and the
bounds into the domain; `#print axioms` is `propext, Classical.choice, Quot.sound`
plus the one `native_decide` axiom (no `sorryAx`).
-/

/-- veripb kernel proof of UNSAT for `k3_2col`'s generic order encoding. -/
def k3KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 6;
rup >= 0 : ~ ;
pol 3 6 + 2 + s;
rup 1 ~x2 >= 1 : ~ 8 1;
rup 1 ~x3 >= 1 : ~ 8 5;
rup 1 ~x2 1 ~x3 >= 2 : 9 10 ~;
pol 4 11 +;
output NONE ;
conclusion UNSAT : 12;
end pseudo-Boolean proof;
"

/-- veripb kernel proof of UNSAT for `k4_3col`'s generic order encoding. -/
def k4KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 22;
rup >= 0 : ~ ;
pol 20 18 + 15 + s;
pol 21 17 + 14 + s 24 + s 13 + 10 + s 7 + s;
pol 5 15 + 9 + 25 + s;
pol 5 18 + 12 + 25 + s 22 + 26 + s;
pol 21 19 + 16 + s 27 + s;
pol 19 12 + 25 + 6 + 25 + s 14 + 8 + s 28 + s;
rup 1 x8 >= 1 : ~ 29 4;
rup 1 ~x1 >= 1 : ~ 29 11;
rup 1 ~x3 >= 1 : ~ 29 17;
rup 1 ~x5 >= 1 : ~ 29 20;
rup 1 ~x4 >= 1 : ~ 31 32 25 6;
rup 1 ~x6 >= 1 : ~ 33 31 25 9;
rup 1 ~x4 1 ~x6 >= 2 : 34 35 ~;
pol 16 36 +;
output NONE ;
conclusion UNSAT : 37;
end pseudo-Boolean proof;
"

/-- **K₃ is not 2-colourable.** -/
theorem k3_2col_unsat : ¬ k3_2col.isSatisfiableInt :=
  csp_unsat k3_2col (VeriPB.Reflect.checkProof_sound _ 3 k3KernelProof (by native_decide))

/-- **K₄ is not 3-colourable.** -/
theorem k4_3col_unsat : ¬ k4_3col.isSatisfiableInt :=
  csp_unsat k4_3col (VeriPB.Reflect.checkProof_sound _ 8 k4KernelProof (by native_decide))

end CSP.L2S.PB.GraphColoring
