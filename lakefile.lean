import Lake
open Lake DSL

package "CSP" where
  version := v!"1.0.0"

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

-- PB (pseudo-Boolean) verified backend dependency: PBLean (Mathlib-free), on the
-- shared Lean 4.30.0 toolchain. Provides VeriPB.Reflect.checkProofBool / checkProof_sound.
require veripb from git
  "https://github.com/leansolving/pblean" @ "v0.3.0"

@[default_target]
lean_lib "CSP" where
  -- add library configuration options here

require "Canonical" from git
  "https://github.com/chasenorman/CanonicalLean" @ "v4.30.0"
