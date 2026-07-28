import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

/-!
# Pigeonhole principle PHP(p,h)

Placing `p` pigeons into `h` holes with no two sharing a hole is impossible when
`p > h` — the standard hard instance for resolution.

One variable per pigeon over `{1,…,h}`, with a single `alldifferent` over them all.

Instances: `php_3_2`, `php_5_4`, `php_7_6`, `php_9_8`, all UNSAT.
-/

-- Pigeon `i` lives in some hole in {1,…,holes}.
def php_bounds (pigeons holes : ℕ) : List (IntConstraint pigeons) :=
  List.finRange pigeons |>.map (fun i => bound i 1 holes)

-- No two pigeons share a hole.
def php_alldiff (pigeons : ℕ) : IntConstraint pigeons :=
  alldifferent (_root_.Vector.ofFn id)

def php_csp (pigeons holes : ℕ) : IntCSP :=
  ⟨pigeons, php_bounds pigeons holes ++ [php_alldiff pigeons]⟩

-- 3 pigeons into 2 holes (UNSAT).
def php_3_2 : IntCSP := php_csp 3 2

-- 5 pigeons into 4 holes (UNSAT).
def php_5_4 : IntCSP := php_csp 5 4

-- 7 pigeons into 6 holes (UNSAT).
def php_7_6 : IntCSP := php_csp 7 6

-- 9 pigeons into 8 holes (UNSAT).
def php_9_8 : IntCSP := php_csp 9 8
