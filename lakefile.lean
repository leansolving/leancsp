import Lake
open Lake DSL

package "CSP" where
  version := v!"1.0.0"

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0"

-- PB (pseudo-Boolean) verified backend dependency: PBLean (Mathlib-free), on the
-- shared Lean 4.30.0 toolchain. Provides VeriPB.Reflect.checkProofBool / checkProof_sound.
--
-- v0.3.1 ships the `VeriPBReflect` lib (`precompileModules`), publishing the checker's kernel
-- closure (PseudoBoolean → FromVeriPB → Reflect) as native code, so `ofReduceBool` reduces
-- `checkProofBool` compiled (~70 s for the 98 MB S(4) cert) instead of interpreted (~21 min).
-- Do not pin below v0.3.1: the experiments' in-Lean checking-time tier assumes the native path
-- (`experiments/run.py` preflights for the `VeriPBReflect` .so).  See `docs/PRECOMPILE_AND_TRUST.md`.
require veripb from git
  "https://github.com/leansolving/pblean" @ "v0.3.1"

@[default_target]
lean_lib "CSP" where
  -- Compile the CSP root *and all submodules* (proofs, L2S, PB backend, tests) on a
  -- bare `lake build` — the default single-root glob would build only `CSP.lean`
  -- (which merely imports Mathlib), silently skipping the actual source. (#28)
  globs := #[.andSubmodules `CSP]

-- Native benchmark harness for `experiments/lib/check_largest.py`: a Mathlib-free executable
-- (imports only veripb) that times the *compiled* `checkProofBool` on a certificate — the same
-- function `Lean.ofReduceBool` reduces. Built on demand via `lake build checkbench`.
lean_exe checkbench where
  srcDir := "experiments/lib"
  root := `CheckBench

require "Canonical" from git
  "https://github.com/chasenorman/CanonicalLean" @ "v4.30.0"
