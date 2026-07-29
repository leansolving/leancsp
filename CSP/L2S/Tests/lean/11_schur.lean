import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

/-!
# Schur numbers

`S(k)` is the largest `n` for which `{1,…,n}` splits into `k` sum-free parts — no
part containing `x, y, z` with `x + y = z`.  Equivalently, colour `1..n` with `c`
colours so no triple `(i, j, i+j)` (including `i = j`) is monochromatic; that is the
`schur_triple` not-all-equal pattern.

Known values: `S(1) = 1`, `S(2) = 4`, `S(3) = 13`, `S(4) = 44`, `S(5) = 160`.
CSPLib problem 015.
-/

-- Create bound constraints for n variables with domain 1..c
def schur_bounds (n c : ℕ) : List (IntConstraint n) :=
  List.finRange n |>.map (fun i => bound i 1 c)

-- Generate all valid sum triples (i, j, k) where i ≤ j and labels satisfy: (i+1)+(j+1)=(k+1)
-- Variables are 0-indexed, but represent balls labeled 1..n
-- So ball at index i has label i+1, and we need (i+1)+(j+1)=(k+1), which gives k=i+j+1.
-- The j = i case is the diagonal x+x=2x triple (e.g. 1+1=2, 2+2=4) and must be included:
-- omitting it would wrongly make {1,…,5} 2-colourable, breaking S(2)=4.
def generate_schur_triples (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  let rec aux (i : ℕ) (acc : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ × ℕ) :=
    if i >= n - 1 then acc
    else
      -- For each i, j ranges from i (so x ≤ y), and i+j+1 < n
      let triples_for_i := List.range (n - i) |>.filterMap fun j_offset =>
        let j := i + j_offset
        -- Ball at index k represents label k+1, so (i+1)+(j+1)=(k+1) gives k=i+j+1
        let sum := i + j + 1
        if sum < n then some (i, j, sum) else none
      aux (i + 1) (acc ++ triples_for_i)
  aux 0 []

-- Helper to create schur_triple constraints with proofs
def make_schur_constraints (n : ℕ) (triples : List (ℕ × ℕ × ℕ)) :
    List (IntConstraint n) :=
  triples.filterMap fun (i, j, k) =>
    if h1 : i < n then
      if h2 : j < n then
        if h3 : k < n then
          some (schur_triple ⟨i, h1⟩ ⟨j, h2⟩ ⟨k, h3⟩)
        else none
      else none
    else none

-- General parametric Schur CSP
def schur_csp (n c : ℕ) : IntCSP :=
  let triples := generate_schur_triples n
  ⟨n, schur_bounds n c ++ make_schur_constraints n triples⟩

-- S(2) = 4: Test with n=4, c=2 (should be solvable)
def schur_2_4 : IntCSP := schur_csp 4 2

-- S(3) = 13: Test with n=13, c=3 (should be solvable)
def schur_3_13 : IntCSP := schur_csp 13 3

-- Small test: n=3, c=2 (definitely solvable, only one triple: (0,1,2))
def schur_small : IntCSP := schur_csp 3 2

-- S(2) = 4: {1,…,5} cannot be 2-coloured sum-free (UNSAT). veripb benchmark `schur5`.
def schur_2_5 : IntCSP := schur_csp 5 2

-- S(3) = 13: {1,…,14} cannot be 3-coloured sum-free (UNSAT). veripb benchmark `schur14_3`.
def schur_3_14 : IntCSP := schur_csp 14 3
