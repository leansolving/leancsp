import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Bounded Model Checking

Traffic light controller: RED(0) → GREEN(2) → YELLOW(1) → RED(0)

Natural encoding using reified implications:
- Variables: state[0], state[1], ..., state[k-1] ∈ {0,1,2}
- Transitions: if state[t] = s then state[t+1] = next(s)
- Safety check: Can we reach state[1]=RED and state[2]=YELLOW?

If UNSAT: transition relation prevents RED→YELLOW. If SAT: bug found.
-/

-- General BMC formulation parameterized by number of time steps
def bounded_model_checking_k (k : ℕ) (h_k : k ≥ 3) : IntCSP :=
  let nvars := k

  -- All state variables have domain {0,1,2}
  let bounds := (List.finRange k).map fun i =>
    bound ⟨i.val, by omega⟩ 0 2

  -- Initial condition: state[0] = RED
  let initial := [equals_const ⟨0, by omega⟩ 0]

  -- Transition relation: RED(0)→GREEN(2), GREEN(2)→YELLOW(1), YELLOW(1)→RED(0)
  -- For each time step t ∈ [0, k-2], add all three transition rules
  let transitions := (List.finRange (k - 1)).flatMap fun t => [
    if_then ⟨t.val, by omega⟩ 0 ⟨t.val + 1, by omega⟩ 2,  -- RED → GREEN
    if_then ⟨t.val, by omega⟩ 2 ⟨t.val + 1, by omega⟩ 1,  -- GREEN → YELLOW
    if_then ⟨t.val, by omega⟩ 1 ⟨t.val + 1, by omega⟩ 0   -- YELLOW → RED
  ]


  let safety_violation := [
    equals_const ⟨1, by omega⟩ 1,  -- state[2] = YELLOW?
  ]

  ⟨nvars, bounds ++ initial ++ transitions ++ safety_violation⟩

-- Instantiate with k=5 time steps
def bounded_model_checking : IntCSP :=
  bounded_model_checking_k 5 (by decide)

def main : IO Unit := do
  saveAllBackendsAutoTimed bounded_model_checking
