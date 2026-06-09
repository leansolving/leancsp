import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Tests.lean.«35_pigeonhole»

namespace CSP.L2S.PB.Pigeonhole

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the pigeonhole corpus

The corpus CSPs `php_3_2`, `php_5_4`, `php_7_6`, `php_9_8`
(`Tests/lean/35_pigeonhole.lean`) — `k+1` pigeons into `k` holes, no two sharing —
are each proved `¬ isSatisfiableInt` by a **single** application of the generic
`csp_unsat` theorem (`GenericEncode.lean`): no per-problem signature, scope,
encoding, or soundness bridge.  The only per-problem datum is the committed kernel
proof string (RoundingSat + veripb, both untrusted), kernel-checked through PBLean's
verified reflection checker via `native_decide`.

Pigeonhole's infeasibility comes entirely from `alldifferent` over a domain smaller
than the number of variables (the canonical resolution-hard instance); the bounds
fix the domain and the generic encoder emits the aux-free `alldifferent` order
encoding.  `csp_unsat csp cert` does the rest, with `#print axioms` =
`propext, Classical.choice, Quot.sound` + the `native_decide` axiom (no `sorryAx`).
-/

/-- The veripb-elaborated kernel proof of UNSAT for `php_3_2`'s order encoding. -/
def phpKernelProof : String :=
"pseudo-Boolean proof version 3.0
f 2;
rup >= 0 : ~ ;
pol 3 1 1000000000000000 * + 2 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 4;
end pseudo-Boolean proof;
"

/-- The veripb-elaborated kernel proof of UNSAT for `php_5_4`'s order encoding. -/
def php5KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 14;
rup >= 0 : ~ ;
pol 15 11 1000000000000000 * + 12 1000000000000000 * + 13 1000000000000000 * + 14 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 16;
end pseudo-Boolean proof;
"

/-- The veripb-elaborated kernel proof of UNSAT for `php_7_6`'s order encoding. -/
def php7KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 34;
rup >= 0 : ~ ;
pol 35 29 1000000000000000 * + 30 1000000000000000 * + 31 1000000000000000 * + 32 1000000000000000 * + 33 1000000000000000 * + 34 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 36;
end pseudo-Boolean proof;
"

/-- The veripb-elaborated kernel proof of UNSAT for `php_9_8`'s order encoding. -/
def php9KernelProof : String :=
"pseudo-Boolean proof version 3.0
f 62;
rup >= 0 : ~ ;
pol 63 55 1000000000000000 * + 56 1000000000000000 * + 57 1000000000000000 * + 58 1000000000000000 * + 59 1000000000000000 * + 60 1000000000000000 * + 61 1000000000000000 * + 62 1000000000000000 * +;
output NONE ;
conclusion UNSAT : 64;
end pseudo-Boolean proof;
"

/-- **Pigeonhole `php_3_2`** (three pigeons, two holes) is unsatisfiable. -/
theorem php_3_2_unsat : ¬ php_3_2.isSatisfiableInt :=
  csp_unsat php_3_2 (VeriPB.Reflect.checkProof_sound _ 3 phpKernelProof (by native_decide))

/-- **Pigeonhole `php_5_4`** (five pigeons, four holes) is unsatisfiable. -/
theorem php_5_4_unsat : ¬ php_5_4.isSatisfiableInt :=
  csp_unsat php_5_4 (VeriPB.Reflect.checkProof_sound _ 15 php5KernelProof (by native_decide))

/-- **Pigeonhole `php_7_6`** (seven pigeons, six holes) is unsatisfiable. -/
theorem php_7_6_unsat : ¬ php_7_6.isSatisfiableInt :=
  csp_unsat php_7_6 (VeriPB.Reflect.checkProof_sound _ 35 php7KernelProof (by native_decide))

/-- **Pigeonhole `php_9_8`** (nine pigeons, eight holes) is unsatisfiable. -/
theorem php_9_8_unsat : ¬ php_9_8.isSatisfiableInt :=
  csp_unsat php_9_8 (VeriPB.Reflect.checkProof_sound _ 63 php9KernelProof (by native_decide))

end CSP.L2S.PB.Pigeonhole
