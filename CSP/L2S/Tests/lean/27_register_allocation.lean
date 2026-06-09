import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Register Allocation

Assign program variables to physical registers respecting live range interference.

Setup: 6 virtual registers → 3 physical registers (r0, r1, r2)
Interference graph has 10 edges (variables live simultaneously)
Pre-coloring: v0=r0, v5=r2 (calling convention)

Variables: 6, domain [0,2]
Constraints: Pre-coloring + interference (graph coloring)
-/

-- Helper to create all variables scope
def allVars6 : _root_.Vector (VarType 6) 6 :=
  _root_.Vector.ofFn id

-- Register allocation CSP (6 virtual registers, 3 physical registers)
def register_allocation : IntCSP :=
  let nvars := 6
  let nregs := 3  -- Physical registers r0, r1, r2

  -- Bounds: each virtual register assigned to physical register in [0, nregs-1]
  let bounds_list := (List.finRange nvars).map fun i =>
    bound i 0 (nregs - 1)

  -- Pre-coloring constraints (calling convention)
  let precolor := [
    equals_const ⟨0, by decide⟩ 0,  -- v0 = r0
    equals_const ⟨5, by decide⟩ 2   -- v5 = r2
  ]

  -- Interference constraints: variables with overlapping live ranges
  -- must be assigned different registers
  let interferences := [
    -- v0 interferences
    not_equal ⟨0, by decide⟩ ⟨1, by decide⟩,  -- v0 ≠ v1
    not_equal ⟨0, by decide⟩ ⟨2, by decide⟩,  -- v0 ≠ v2
    not_equal ⟨0, by decide⟩ ⟨3, by decide⟩,  -- v0 ≠ v3
    -- v1 interferences
    not_equal ⟨1, by decide⟩ ⟨2, by decide⟩,  -- v1 ≠ v2
    not_equal ⟨1, by decide⟩ ⟨4, by decide⟩,  -- v1 ≠ v4
    -- v2 interferences
    not_equal ⟨2, by decide⟩ ⟨3, by decide⟩,  -- v2 ≠ v3
    not_equal ⟨2, by decide⟩ ⟨4, by decide⟩,  -- v2 ≠ v4
    not_equal ⟨2, by decide⟩ ⟨5, by decide⟩,  -- v2 ≠ v5
    -- v3 interferences
    not_equal ⟨3, by decide⟩ ⟨5, by decide⟩,  -- v3 ≠ v5
    -- v4 interferences
    not_equal ⟨4, by decide⟩ ⟨5, by decide⟩   -- v4 ≠ v5
  ]

  -- Optional: Register pressure constraint
  -- Limit how many variables can be in the same register
  -- (in practice, this is implicitly handled by interference graph)

  ⟨nvars, bounds_list ++ precolor ++ interferences⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed register_allocation
