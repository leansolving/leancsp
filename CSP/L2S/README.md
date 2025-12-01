# L2S: LeanToSolver

L2S is a subformalization of CSPs where every problem can be automatically translated to MiniZinc or SMT-LIB for solving. It provides:

- **HomogeneousCSP**: CSPs with integer variables and individual bounds
- **TaggedConstraint**: Dual representation (semantic pattern + executable checker)
- **Multi-backend translation**: Unified API for MiniZinc and SMT-LIB output

## Quick Start

```lean
import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Translate

open CSP.L2S

def my_csp : HomogeneousCSP :=
  ⟨4, [bound 0 1 10, bound 1 1 10, bound 2 1 10, bound 3 1 10,
       alldifferent (_root_.Vector.ofFn id),
       sum_eq (_root_.Vector.ofFn id) 20]⟩

def main : IO Unit := do
  saveTo my_csp "model.mzn" BackendType.MiniZinc
  saveTo my_csp "model.smt2" BackendType.SMTLIB
```

## Available Constraints

| Category | Constraints |
|----------|-------------|
| **Global** | `alldifferent`, `increasing`, `count`, `count_var`, `element`, `maximum`, `minimum` |
| **Arithmetic** | `sum_eq/le/lt/ge/gt/ne`, `linear_eq/le/lt/ge/gt/ne` |
| **Bounds** | `bound` |
| **Binary comparisons** | `equal`, `not_equal`, `less_than`, `less_equal`, `greater_than`, `greater_equal` |
| **Unary comparisons** | `equals_const`, `not_equals_const`, `less_than_const`, `less_equal_const`, `greater_than_const`, `greater_equal_const` |
| **Boolean gates** | `not_gate`, `and_gate`, `or_gate`, `xor_gate`, `nand_gate`, `nor_gate` |
| **Multi-input logic** | `and_all`, `or_all`, `xor_all` |
| **Implication** | `implies`, `iff`, `if_then`, `if_then_or` |
| **Cardinality** | `at_least_k`, `at_most_k`, `exactly_k` |
| **Variable targets** | `sum_rel_var`, `linear_rel_var`, `product_rel_var` |
| **Absolute value** | `abs_diff_eq/le/ge`, `abs_diff_var` |
| **Sliding window** | `sliding_sum`, `sliding_sum_le`, `sliding_sum_eq` |
| **Scheduling** | `disjunctive` |
| **Special** | `schur_triple`, `alldifferent_diag_pos/neg`, `modulo` |

## Translation API

```lean
-- To string
translateTo csp BackendType.MiniZinc    -- MiniZinc output
translateTo csp BackendType.SMTLIB      -- SMT-LIB output

-- To file
saveTo csp "path.mzn" BackendType.MiniZinc
saveTo csp "path.smt2" BackendType.SMTLIB
```

## Adding New Constraints

1. Add pattern to `ConstraintPattern` in `Core.lean`
2. Create constructor in `Constraints.lean`
3. Add translation in `Backends/MiniZinc.lean` and `Backends/SMTLIB.lean`
