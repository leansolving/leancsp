import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Monster Defence Puzzle

Alldifferent with heterogeneous domains: X∈{1,2,3}, Y∈{2,3}, Z∈{2,3}, T∈{1..5}, U∈{3..6}.
-/

def heterogeneous_bounds (domains : List (ℤ × ℤ)) :
    List (TaggedConstraint domains.length) :=
  (List.finRange domains.length).map fun i =>
    let (lb, ub) := domains[i.val]!
    bound i lb ub

def alldifferent_heterogeneous_csp (domains : List (ℤ × ℤ)) : HomogeneousCSP :=
  let n := domains.length
  ⟨n, heterogeneous_bounds domains ++ [alldifferent (_root_.Vector.ofFn id)]⟩

def monster_defence : HomogeneousCSP :=
  let domains := [(1, 3), (2, 3), (2, 3), (1, 5), (3, 6)]
  alldifferent_heterogeneous_csp domains

def main : IO Unit := do
  saveAllBackendsAutoTimed monster_defence
