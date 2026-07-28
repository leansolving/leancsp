import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry

open CSP.L2S

/-!
# Magic sequence

A sequence `[x0, …, x_{n-1}]` where each `x_i` equals the number of occurrences of
the value `i` in the sequence.  Here `n = 10`, domains `0..10`, with one `count`
constraint per position.
-/

-- Helper to create bound constraints for all n variables
def magic_bounds (n : ℕ) : List (IntConstraint n) :=
  List.finRange n |>.map (fun i => bound i 0 n)

-- Helper to create count_var constraints for magic sequence
-- For each i in 0..n-1: count(all_vars, i, x[i])
def magic_count_constraints (n : ℕ) : List (IntConstraint n) :=
  let all_vars : _root_.Vector (VarType n) n := _root_.Vector.ofFn id
  List.finRange n |>.map fun i =>
    count_var all_vars (i.val : ℤ) i

-- General parametric magic sequence CSP
def magic_sequence_csp (n : ℕ) : IntCSP :=
  ⟨n, magic_bounds n ++ magic_count_constraints n⟩

-- Specific instance: n=10
def magicseq10 : IntCSP := magic_sequence_csp 10
