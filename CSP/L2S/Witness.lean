import CSP.L2S.Core
import Lean

/-!
# SAT witness loader (untrusted producer, kernel-checked)

The satisfiability analogue of `csp_unsat_file`.  An external solver is run outside
Lean to produce a candidate assignment, written to a space-separated `.sol` file (one
value per variable, in variable order).  At elaboration time `csp_sat_file` reads it,
builds the `IntAssignment`, and proves `IntCSP.isSatisfiableInt` by kernel `decide`.

The solver is fully untrusted: a wrong witness simply fails `decide`, never yields an
unsound theorem.  This path uses no `native_decide` / `ofReduceBool`, so
witness-checked theorems stay axiom-clean.

Witness files store non-negative integer tokens; other tokens are skipped.
-/

namespace CSP.L2S

open Lean Elab Term

/-- Read a `.sol` file at elaboration time and produce a `List Int` literal.
    File format: whitespace-separated non-negative integers.  The path is resolved
    relative to the build's working directory (the project root), like the external
    toolchain scripts — *not* relative to the calling `.lean` file. -/
elab "solFromFile" path:str : term => do
  let filePath := path.getString
  let content ← IO.FS.readFile ⟨filePath⟩
  let normalized := (content.replace "\n" " ").replace "\t" " "
  let vals := (normalized.splitOn " ").filterMap String.toNat?
  let intExprs := vals.map fun v =>
    Lean.mkApp (Lean.mkConst ``Int.ofNat) (Lean.mkNatLit v)
  let listType := Lean.mkConst ``Int
  let expr := intExprs.foldr
    (fun hd tl => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) listType hd tl)
    (Lean.mkApp (Lean.mkConst ``List.nil [.zero]) listType)
  return expr

/-- Build an assignment from a list of values: variable `i` gets `l[i]` (default `0`). -/
def assignmentOfList (n : ℕ) (l : List Int) : IntAssignment n := fun i => l.getD i.val 0

-- Decidability of solution checking (so `by decide` discharges the witness).
-- `satisfiesConstraintInt`/`isSolutionInt` are `def`s, hence not unfolded during instance
-- synthesis; these make the underlying `patternHolds`/`List.decidableBAll` instances visible.

instance decSatisfiesConstraintInt {n : ℕ} (c : IntConstraint n) (a : IntAssignment n) :
    Decidable (IntCSP.satisfiesConstraintInt c a) :=
  inferInstanceAs (Decidable (patternHolds c a))

instance decIsSolutionInt (csp : IntCSP) (a : IntAssignment csp.num_vars) :
    Decidable (IntCSP.isSolutionInt csp a) :=
  inferInstanceAs (Decidable (∀ c ∈ csp.constraints, IntCSP.satisfiesConstraintInt c a))

/-- **SAT via an external witness.**  `csp_sat_file csp "path/to/witness.sol"` proves
    `csp.isSatisfiableInt` by loading the committed witness and kernel-checking it. -/
macro "csp_sat_file " csp:term:max path:str : term =>
  `(show CSP.L2S.IntCSP.isSatisfiableInt $csp from
      ⟨CSP.L2S.assignmentOfList _ (solFromFile $path), by decide⟩)

end CSP.L2S
