import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Pigeonhole Principle PHP(p,h)

## Problem Description
Placing `p` pigeons into `h` holes with no two pigeons sharing a hole is
impossible whenever `p > h`. This is the canonical hard instance for resolution
and a standard pseudo-Boolean benchmark.

## CSP Formulation
- **Variables**: one per pigeon (1..p, 0-indexed).
- **Domain**: {1,…,h} (the hole each pigeon occupies).
- **Constraint**: `alldifferent` over all pigeon variables (no shared hole).

When `p > h` the `alldifferent` over a domain of size `h < p` is unsatisfiable —
the pigeonhole principle in its most direct CSP form. (veripb's `php32`
benchmark uses the one-hot pseudo-Boolean encoding of the same fact.)

## Instances
- `php_3_2` : 3 pigeons, 2 holes — **UNSAT**.
- `php_5_4` : 5 pigeons, 4 holes — **UNSAT**.
- `php_7_6` : 7 pigeons, 6 holes — **UNSAT**.
- `php_9_8` : 9 pigeons, 8 holes — **UNSAT**.

## Constraint families
`bound`, `alldifferent`.
-/

-- Pigeon `i` lives in some hole in {1,…,holes}.
def php_bounds (pigeons holes : ℕ) : List (TaggedConstraint pigeons) :=
  List.finRange pigeons |>.map (fun i => bound i 1 holes)

-- No two pigeons share a hole.
def php_alldiff (pigeons : ℕ) : TaggedConstraint pigeons :=
  alldifferent (_root_.Vector.ofFn id)

def php_csp (pigeons holes : ℕ) : HomogeneousCSP :=
  ⟨pigeons, php_bounds pigeons holes ++ [php_alldiff pigeons]⟩

-- 3 pigeons into 2 holes (UNSAT).
def php_3_2 : HomogeneousCSP := php_csp 3 2

-- 5 pigeons into 4 holes (UNSAT).
def php_5_4 : HomogeneousCSP := php_csp 5 4

-- 7 pigeons into 6 holes (UNSAT).
def php_7_6 : HomogeneousCSP := php_csp 7 6

-- 9 pigeons into 8 holes (UNSAT).
def php_9_8 : HomogeneousCSP := php_csp 9 8

def main : IO Unit := do
  saveAllBackendsAutoTimed php_3_2
