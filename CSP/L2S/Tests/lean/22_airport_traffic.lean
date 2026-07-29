import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

/-!
# Airport Traffic Control

Schedule aircraft movements on taxiways avoiding collisions.

Setup: 2 aircraft traverse 4 segments (S0→S1→S2→S3) over 5 time steps.
Each aircraft can advance one segment or wait per time step.

Variables: 10 (2 aircraft × 5 time steps), position ∈ {0,1,2,3,4}
Constraints: Initial positions, movement rules, collision avoidance, goal (reach S3)
-/

-- Airport ground traffic control CSP (2 aircraft, 5 time steps)
def airport_traffic : IntCSP :=
  let naircraft := 2
  let nsteps := 5
  let nvars := naircraft * nsteps  -- 10 variables
  let nsegments := 4  -- S0, S1, S2, S3

  -- Position encoding: 0=S0, 1=S1, 2=S2, 3=S3, 4=completed/off-taxiway
  let bounds_list := (List.finRange nvars).map fun i =>
    bound i 0 4

  -- Initial state: both aircraft at segment 0
  let initial_state := [
    equals_const ⟨0, by decide⟩ 0,  -- A0 starts at S0
    equals_const ⟨5, by decide⟩ 0   -- A1 starts at S0
  ]

  -- Movement constraints: can only advance one segment per step or stay
  -- pos[a][t+1] ∈ {pos[a][t], pos[a][t]+1}
  -- Encoded as: pos[a][t+1] ≥ pos[a][t] AND pos[a][t+1] ≤ pos[a][t]+1
  let movement_constraints := [
    -- A0 step 0→1
    linear_le ⟨#[⟨0, by decide⟩, ⟨1, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨1, by decide⟩, ⟨0, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1,
    -- A0 step 1→2
    linear_le ⟨#[⟨1, by decide⟩, ⟨2, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨2, by decide⟩, ⟨1, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1,
    -- A0 step 2→3
    linear_le ⟨#[⟨2, by decide⟩, ⟨3, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨3, by decide⟩, ⟨2, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1,
    -- A0 step 3→4
    linear_le ⟨#[⟨3, by decide⟩, ⟨4, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨4, by decide⟩, ⟨3, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1,
    -- A1 step 0→1
    linear_le ⟨#[⟨5, by decide⟩, ⟨6, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨6, by decide⟩, ⟨5, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1,
    -- A1 step 1→2
    linear_le ⟨#[⟨6, by decide⟩, ⟨7, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨7, by decide⟩, ⟨6, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1,
    -- A1 step 2→3
    linear_le ⟨#[⟨7, by decide⟩, ⟨8, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨8, by decide⟩, ⟨7, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1,
    -- A1 step 3→4
    linear_le ⟨#[⟨8, by decide⟩, ⟨9, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 0,
    linear_le ⟨#[⟨9, by decide⟩, ⟨8, by decide⟩], rfl⟩ ⟨#[1, -1], rfl⟩ 1
  ]

  -- Collision avoidance: at each time step, aircraft can't be at same position
  -- pos[A0][t] ≠ pos[A1][t] for t = 0..4
  let collision_avoidance := [
    not_equal ⟨0, by decide⟩ ⟨5, by decide⟩,  -- t=0
    not_equal ⟨1, by decide⟩ ⟨6, by decide⟩,  -- t=1
    not_equal ⟨2, by decide⟩ ⟨7, by decide⟩,  -- t=2
    not_equal ⟨3, by decide⟩ ⟨8, by decide⟩,  -- t=3
    not_equal ⟨4, by decide⟩ ⟨9, by decide⟩   -- t=4
  ]

  -- Goal: both aircraft must reach at least segment 3 by end
  -- pos[A0][4] ≥ 3 AND pos[A1][4] ≥ 3
  let goal_constraints := [
    linear_le  -- -pos[A0][4] ≤ -3
      ⟨#[⟨4, by decide⟩], rfl⟩
      ⟨#[-1], rfl⟩
      (-3),
    linear_le  -- -pos[A1][4] ≤ -3
      ⟨#[⟨9, by decide⟩], rfl⟩
      ⟨#[-1], rfl⟩
      (-3)
  ]

  ⟨nvars, bounds_list ++ initial_state ++ movement_constraints ++
          collision_avoidance ++ goal_constraints⟩
