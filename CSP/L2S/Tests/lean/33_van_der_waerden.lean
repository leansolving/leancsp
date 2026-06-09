import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Van der Waerden Numbers W(2,3)

## Problem Description
The van der Waerden number W(r,k) is the smallest n such that every r-colouring
of {1,…,n} contains a monochromatic arithmetic progression of length k.
W(2,3) = 9: every 2-colouring of {1,…,9} has a monochromatic 3-term AP, while
{1,…,8} can be coloured avoiding one.

## CSP Formulation
- **Variables**: one per integer 1..n (0-indexed: variable `i` is integer `i+1`).
- **Domain**: {0,1} (the two colours).
- **Constraint**: for each 3-term AP (a, a+d, a+2d) with a+2d ≤ n,
  the three colours are **not all equal** — exactly the `schur_triple` pattern
  (¬(x = y ∧ y = z)) applied to the AP's three variables.

## Instances
- `vdw_2_3_8` : {1,…,8}, 2 colours — **SAT** (witness RRBBRRBB).
- `vdw_2_3_9` : {1,…,9}, 2 colours — **UNSAT** (this is W(2,3) = 9).

## Showcase
PBLean / veripb benchmark `vdw9` (the W(2,3) upper-bound certificate).

## Constraint families
`bound`, `schur_triple` (3-ary not-all-equal).
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

def main : IO Unit := do
  saveAllBackendsAutoTimed vdw_2_3_9
