import Lake
open Lake DSL

package "CSP" where
  version := v!"1.0.0"

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

-- PB (pseudo-Boolean) verified backend dependency. Re-enabled once PBLean is on
-- Lean 4.30.0 (upstream bump from 4.28). Must share the project toolchain.
-- require veripb from "/Users/szeider/work/pblean-4.30"

@[default_target]
lean_lib "CSP" where
  -- add library configuration options here

require "Canonical" from git
  "https://github.com/chasenorman/CanonicalLean" @ "v4.30.0"
