import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Railway Interlocking

Verify safety of railway track switching system.

Two conflicting routes share segments S0, S1:
- Route A: S0 → S1 → S2 (straight, point=0)
- Route B: S0 → S1 → S3 (diverge, point=1)

Variable layout:
- v0: route_A active (Boolean)
- v1: route_B active (Boolean)
- v2: segment_S0 reserved (Boolean)
- v3: segment_S1 reserved (Boolean)
- v4: segment_S2 reserved (Boolean)
- v5: segment_S3 reserved (Boolean)
- v6: point_P1 position (0=normal/straight, 1=reverse/diverge)

Constraints: Route mutex, segment reservation implications, point consistency
-/

def railway_interlocking : HomogeneousCSP :=
  let nvars := 7

  -- All variables are Boolean: 0 or 1
  let bounds := (List.finRange nvars).map fun i =>
    bound ⟨i.val, by omega⟩ 0 1

  -- Safety constraint 1: Conflicting routes are mutually exclusive
  -- route_A + route_B ≤ 1 (can't both be active)
  let route_mutex := [
    linear_le
      ⟨#[⟨0, by decide⟩, ⟨1, by decide⟩], rfl⟩
      ⟨#[1, 1], rfl⟩
      1
  ]

  -- Route A implications: if route_A active, then its segments are reserved
  -- Using if_then for clarity: route_A = 1 → segment = 1
  let route_a_segments := [
    if_then ⟨0, by decide⟩ 1 ⟨2, by decide⟩ 1,  -- route_A → segment_S0
    if_then ⟨0, by decide⟩ 1 ⟨3, by decide⟩ 1,  -- route_A → segment_S1
    if_then ⟨0, by decide⟩ 1 ⟨4, by decide⟩ 1   -- route_A → segment_S2
  ]

  -- Route B implications: if route_B active, then its segments are reserved
  let route_b_segments := [
    if_then ⟨1, by decide⟩ 1 ⟨2, by decide⟩ 1,  -- route_B → segment_S0
    if_then ⟨1, by decide⟩ 1 ⟨3, by decide⟩ 1,  -- route_B → segment_S1
    if_then ⟨1, by decide⟩ 1 ⟨5, by decide⟩ 1   -- route_B → segment_S3
  ]

  -- Point consistency: route determines point position
  -- If route_A active, point must be normal (0)
  -- If route_B active, point must be reverse (1)
  let point_constraints := [
    if_then ⟨0, by decide⟩ 1 ⟨6, by decide⟩ 0,  -- route_A → point_P1 = 0 (normal)
    if_then ⟨1, by decide⟩ 1 ⟨6, by decide⟩ 1   -- route_B → point_P1 = 1 (reverse)
  ]

  -- Operational constraint: at least one route should be active
  -- (for interesting instance, otherwise trivial solution is all 0)
  let operational := [
    linear_le  -- route_A + route_B ≥ 1, i.e., -(route_A + route_B) ≤ -1
      ⟨#[⟨0, by decide⟩, ⟨1, by decide⟩], rfl⟩
      ⟨#[-1, -1], rfl⟩
      (-1)
  ]

  ⟨nvars, bounds ++ route_mutex ++ route_a_segments ++ route_b_segments ++
          point_constraints ++ operational⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed railway_interlocking
