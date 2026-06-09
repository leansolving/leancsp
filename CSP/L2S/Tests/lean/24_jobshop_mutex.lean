import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Job-Shop Scheduling

Schedule jobs on machines with precedence and mutex constraints.

Instance: 3 jobs, 3 machines
- Job 0: M1(3) → M0(2) → M2(2)
- Job 1: M0(2) → M2(1) → M1(4)
- Job 2: M1(2) → M2(4) → M0(3)

Variables: 9 task start times
Constraints: Task precedence, machine mutex (using disjunctive), makespan deadline
-/

-- Job-shop scheduling with flexible machine orderings
def jobshop_mutex : IntCSP :=
  let njobs := 3
  let ntasks_per_job := 3
  let nvars := njobs * ntasks_per_job  -- 9 variables
  let horizon := 20  -- Time horizon

  -- Task data: (machine, duration)
  -- Job 0: M1→M0→M2 with durations 3,2,2
  -- Job 1: M0→M2→M1 with durations 2,1,4
  -- Job 2: M1→M2→M0 with durations 2,4,3

  -- Bounds: all start times in [0, horizon]
  let bounds_list := [
    bound ⟨0, by decide⟩ 0 horizon, bound ⟨1, by decide⟩ 0 horizon,
    bound ⟨2, by decide⟩ 0 horizon, bound ⟨3, by decide⟩ 0 horizon,
    bound ⟨4, by decide⟩ 0 horizon, bound ⟨5, by decide⟩ 0 horizon,
    bound ⟨6, by decide⟩ 0 horizon, bound ⟨7, by decide⟩ 0 horizon,
    bound ⟨8, by decide⟩ 0 horizon
  ]

  -- Precedence constraints: s[j][t+1] ≥ s[j][t] + duration[j][t]
  -- Job 0: v1 ≥ v0 + 3, v2 ≥ v1 + 2
  -- Job 1: v4 ≥ v3 + 2, v5 ≥ v4 + 1
  -- Job 2: v7 ≥ v6 + 2, v8 ≥ v7 + 4
  let precedence := [
    -- Job 0 precedence
    linear_le
      ⟨#[⟨0, by decide⟩, ⟨1, by decide⟩], rfl⟩
      ⟨#[1, -1], rfl⟩
      (-3),  -- v0 - v1 ≤ -3, i.e., v1 ≥ v0 + 3
    linear_le
      ⟨#[⟨1, by decide⟩, ⟨2, by decide⟩], rfl⟩
      ⟨#[1, -1], rfl⟩
      (-2),  -- v1 - v2 ≤ -2, i.e., v2 ≥ v1 + 2
    -- Job 1 precedence
    linear_le
      ⟨#[⟨3, by decide⟩, ⟨4, by decide⟩], rfl⟩
      ⟨#[1, -1], rfl⟩
      (-2),  -- v3 - v4 ≤ -2, i.e., v4 ≥ v3 + 2
    linear_le
      ⟨#[⟨4, by decide⟩, ⟨5, by decide⟩], rfl⟩
      ⟨#[1, -1], rfl⟩
      (-1),  -- v4 - v5 ≤ -1, i.e., v5 ≥ v4 + 1
    -- Job 2 precedence
    linear_le
      ⟨#[⟨6, by decide⟩, ⟨7, by decide⟩], rfl⟩
      ⟨#[1, -1], rfl⟩
      (-2),  -- v6 - v7 ≤ -2, i.e., v7 ≥ v6 + 2
    linear_le
      ⟨#[⟨7, by decide⟩, ⟨8, by decide⟩], rfl⟩
      ⟨#[1, -1], rfl⟩
      (-4)   -- v7 - v8 ≤ -4, i.e., v8 ≥ v7 + 4
  ]

  -- Machine mutex using disjunctive
  -- Machine 0 (M0): tasks v1 (dur=2), v3 (dur=2), v8 (dur=3)
  -- Machine 1 (M1): tasks v0 (dur=3), v5 (dur=4), v6 (dur=2)
  -- Machine 2 (M2): tasks v2 (dur=2), v4 (dur=1), v7 (dur=4)

  let machine_mutex := [
    -- Machine 0: flexible ordering for v1, v3, v8
    disjunctive [⟨1, by decide⟩, ⟨3, by decide⟩, ⟨8, by decide⟩] [2, 2, 3],
    -- Machine 1: flexible ordering for v0, v5, v6
    disjunctive [⟨0, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩] [3, 4, 2],
    -- Machine 2: flexible ordering for v2, v4, v7
    disjunctive [⟨2, by decide⟩, ⟨4, by decide⟩, ⟨7, by decide⟩] [2, 1, 4]
  ]

  -- Makespan constraint (all jobs finish by deadline)
  let deadline := 15
  let makespan_constraints := [
    linear_le  -- v2 + 2 ≤ 15 (job 0 completion)
      ⟨#[⟨2, by decide⟩], rfl⟩
      ⟨#[1], rfl⟩
      (deadline - 2),
    linear_le  -- v5 + 4 ≤ 15 (job 1 completion)
      ⟨#[⟨5, by decide⟩], rfl⟩
      ⟨#[1], rfl⟩
      (deadline - 4),
    linear_le  -- v8 + 3 ≤ 15 (job 2 completion)
      ⟨#[⟨8, by decide⟩], rfl⟩
      ⟨#[1], rfl⟩
      (deadline - 3)
  ]

  ⟨nvars, bounds_list ++ precedence ++ machine_mutex ++ makespan_constraints⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed jobshop_mutex
