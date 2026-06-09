import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Mutual Exclusion Verification

Two processes compete for a critical section.
States: 0=idle, 1=trying, 2=critical

Non-deterministic state transitions (for each process):
- IDLE (0) → {IDLE, TRYING} (may stay idle or request critical section)
- TRYING (1) → {TRYING, CRITICAL} (may wait or enter critical section)
- CRITICAL (2) → {IDLE} (must exit to idle)

Safety property: Both processes can't be in critical section simultaneously.

If UNSAT: mutual exclusion holds. If SAT: safety violation found.
-/

-- Parameterized mutual exclusion verification
def peterson_mutex_k (k : ℕ) (h_k : k ≥ 2) : IntCSP :=
  let nprocesses := 2
  let nvars := nprocesses * k

  -- Each variable can be in states {0=idle, 1=trying, 2=critical}
  let bounds := (List.finRange nvars).map fun i =>
    bound ⟨i.val, by omega⟩ 0 2

  -- Initial state: both processes idle
  let initial := [
    equals_const ⟨0, by omega⟩ 0,  -- P0 starts idle
    equals_const ⟨k, by omega⟩ 0   -- P1 starts idle
  ]

  -- State machine transitions for Process 0 using if_then_or
  -- Each constraint: if state[t] = s then state[t+1] ∈ successors(s)
  let p0_transitions := (List.finRange (k - 1)).flatMap fun t => [
    if_then_or ⟨t.val, by omega⟩ 0 ⟨t.val + 1, by omega⟩ [0, 1],  -- IDLE → {IDLE, TRYING}
    if_then_or ⟨t.val, by omega⟩ 1 ⟨t.val + 1, by omega⟩ [1, 2],  -- TRYING → {TRYING, CRITICAL}
    if_then_or ⟨t.val, by omega⟩ 2 ⟨t.val + 1, by omega⟩ [0]      -- CRITICAL → {IDLE}
  ]

  -- State machine transitions for Process 1 (offset by k)
  let p1_transitions := (List.finRange (k - 1)).flatMap fun t => [
    if_then_or ⟨k + t.val, by omega⟩ 0 ⟨k + t.val + 1, by omega⟩ [0, 1],  -- IDLE → {IDLE, TRYING}
    if_then_or ⟨k + t.val, by omega⟩ 1 ⟨k + t.val + 1, by omega⟩ [1, 2],  -- TRYING → {TRYING, CRITICAL}
    if_then_or ⟨k + t.val, by omega⟩ 2 ⟨k + t.val + 1, by omega⟩ [0]      -- CRITICAL → {IDLE}
  ]

  -- Safety violation we're checking for
  -- We search for: ∃t. state[P0][t] = 2 ∧ state[P1][t] = 2
  -- Check at time step k-1 (final step)
  let safety_violation := [
    equals_const ⟨k - 1, by omega⟩ 2,      -- P0 in critical section
    equals_const ⟨2 * k - 1, by omega⟩ 2   -- P1 in critical section
  ]

  ⟨nvars, bounds ++ initial ++ p0_transitions ++ p1_transitions ++ safety_violation⟩

-- Instantiate with k=3 time steps
def peterson_mutex : IntCSP :=
  peterson_mutex_k 3 (by decide)

def main : IO Unit := do
  saveAllBackendsAutoTimed peterson_mutex
