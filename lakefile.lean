import Lake
open Lake DSL

package "CSP" where
  version := v!"1.0.0"

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

-- PBLean: the verified VeriPB proof checker (`checkProofBool` / `checkProof_sound`).
-- Keep at v0.3.1 or later — earlier tags lack the precompiled `VeriPBReflect` library,
-- without which certificate checking falls back to the interpreter.
require veripb from git
  "https://github.com/leansolving/pblean" @ "v0.3.1"

@[default_target]
lean_lib "CSP" where
  -- Build the root *and all submodules*, so a bare `lake build` re-checks every
  -- committed certificate; the default single-root glob would compile only `CSP.lean`.
  globs := #[.andSubmodules `CSP]

-- Times the compiled `checkProofBool` on a certificate; used by the experiments.
lean_exe checkbench where
  srcDir := "experiments/lib"
  root := `CheckBench
