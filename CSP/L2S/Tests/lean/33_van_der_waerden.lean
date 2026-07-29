import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

/-!
# Van der Waerden numbers W(2,3)

`W(r,k)` is the least `n` such that every `r`-colouring of `{1,…,n}` contains a
monochromatic `k`-term arithmetic progression.  `W(2,3) = 9`.

One variable per integer (variable `i` is integer `i+1`) over `{0,1}`, with a
`schur_triple` not-all-equal constraint on each 3-term AP `(a, a+d, a+2d)`.

Instances: `vdw_2_3_8` is SAT (witness `RRBBRRBB`), `vdw_2_3_9` is UNSAT.
-/

-- Each integer 1..n gets a Boolean colour variable (domain {0,1}).
def vdw_bounds (n : ℕ) : List (IntConstraint n) :=
  List.finRange n |>.map (fun i => bound i 0 1)

-- All 3-term APs (a, a+d, a+2d) within 1..n, as 0-indexed variable triples.
def vdw_ap_triples (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun i =>
    (List.range n).filterMap fun d0 =>
      let d := d0 + 1
      let j := i + d
      let k := i + 2 * d
      if k < n then some (i, j, k) else none

-- "No monochromatic 3-AP" = not-all-equal over each AP's three colour variables.
def vdw_constraints (n : ℕ) (triples : List (ℕ × ℕ × ℕ)) : List (IntConstraint n) :=
  triples.filterMap fun (i, j, k) =>
    if h1 : i < n then
      if h2 : j < n then
        if h3 : k < n then
          some (schur_triple ⟨i, h1⟩ ⟨j, h2⟩ ⟨k, h3⟩)
        else none
      else none
    else none

def vdw_csp (n : ℕ) : IntCSP :=
  ⟨n, vdw_bounds n ++ vdw_constraints n (vdw_ap_triples n)⟩

-- {1,…,8} is still colourable without a monochromatic 3-AP (SAT).
def vdw_2_3_8 : IntCSP := vdw_csp 8

-- W(2,3) = 9: {1,…,9} forces a monochromatic 3-AP (UNSAT).
def vdw_2_3_9 : IntCSP := vdw_csp 9
