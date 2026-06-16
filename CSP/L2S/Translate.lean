import CSP.L2S.Backend
import CSP.L2S.Backends.MiniZinc
import CSP.L2S.Backends.SMTLIB

namespace CSP.L2S

/-!
# Unified Translation API

All CSP translation functions in one place. Provides:
- **Unified API**: `translateTo` for all backends
- **Extended features**: Objectives, utility functions

## Design

This module sits "above" the backend implementations and provides all
translation entry points. It breaks the circular dependency by:
- `Backend.lean` defines the interface (imported by backend implementations)
- `Backends/MiniZinc.lean` and `Backends/SMTLIB.lean` implement the interface
- `Translate.lean` (this file) imports everything and provides all APIs


## Adding New Backends

1. Create `CSP/Backends/Backends/YourBackend.lean`
2. Implement the `Backend` interface
3. Add constructor to `BackendType` in `Backend.lean`
4. Add case to `selectBackend` below
5. That's it! No other changes needed.
-/

-- ============================================================================
-- Backend Selection
-- ============================================================================

/-- Select the backend implementation for a given backend type -/
def selectBackend : BackendType → Backend
  | BackendType.MiniZinc => MiniZinc.miniZincBackend
  | BackendType.SMTLIB => SMTLIB.smtlibBackend

-- ============================================================================
-- Unified Translation Functions
-- ============================================================================

def translateToExcept (csp : IntCSP)
                      (backendType : BackendType)
                      (opts : BackendOptions := default)
                      : Except TranslatorError String :=
  translateWith (selectBackend backendType) opts csp


def translateTo (csp : IntCSP)
                (backendType : BackendType)
                (opts : BackendOptions := default)
                : String :=
  match translateToExcept csp backendType opts with
  | .ok s => s
  | .error e =>
      let commentPrefix := match backendType with
        | BackendType.MiniZinc => "%"
        | BackendType.SMTLIB => ";"
      s!"{commentPrefix} Translation error: {e.msg}"

-- ============================================================================
-- File I/O Functions
-- ============================================================================

/--
Save a translated CSP to a file.

Creates parent directories automatically if they don't exist.
Prints the output path for confirmation.

## Parameters
- `csp`: The CSP to translate
- `filepath`: Path where to save the file (e.g., "output/model.mzn")
- `backendType`: Which solver format to generate
- `opts`: Backend options (optional)

## Example
```lean
saveTo myCSP "output/queens.mzn" BackendType.MiniZinc
-- Output: ✓ Saved to output/queens.mzn
```
-/
def saveTo (csp : IntCSP)
           (filepath : String)
           (backendType : BackendType)
           (opts : BackendOptions := default)
           : IO Unit := do
  -- Create parent directories if needed
  let fp := System.FilePath.mk filepath
  if let some parent := fp.parent then
    IO.FS.createDirAll parent

  -- Translate and write
  let content := translateTo csp backendType opts
  IO.FS.writeFile filepath content
  IO.println s!"✓ Saved to {filepath}"

/--
Save a translated CSP with automatic file extension.

Automatically appends the correct extension (.mzn or .smt2) based on backend type.
Creates parent directories automatically if they don't exist.
-/
def saveToAuto (csp : IntCSP)
               (basename : String)
               (backendType : BackendType)
               (opts : BackendOptions := default)
               : IO Unit := do
  let ext := getBackendExtension backendType
  let filepath := s!"{basename}.{ext}"
  saveTo csp filepath backendType opts

-- ============================================================================
-- MiniZinc Functions
-- ============================================================================


def translateToMiniZinc (csp : IntCSP) : String :=
  translateTo csp BackendType.MiniZinc

/-- Solving objectives for MiniZinc optimization problems -/
inductive SolveObjective where
  | Satisfy
  | Minimize (expr : String)
  | Maximize (expr : String)
  deriving Repr

/-- MiniZinc translation with custom objective -/
def translateToMiniZincWithObjective (csp : IntCSP)
    (objective : SolveObjective := .Satisfy) : String :=
  -- Include statements
  let includes := MiniZinc.getRequiredIncludes csp

  -- Variable declarations with individual bounds
  let bounds := csp.extractAllBounds
  let varDecls := List.ofFn fun (i : Fin csp.num_vars) =>
    let (lb, ub) := bounds i
    s!"var {lb}..{ub}: x{i.val};"

  -- Constraint translations (excluding bound constraints)
  let constraints := csp.constraints.filterMap fun tc =>
    match tc with
    | IntConstraint.bound _ _ _ => none
    | _ =>
        match MiniZinc.patternToMiniZinc default tc with
        | .ok lines => some (String.intercalate "\n" lines)
        | .error _ => none

  -- Solve statement based on objective
  let solveStmt := match objective with
    | .Satisfy => "solve satisfy;"
    | .Minimize expr => s!"solve minimize {expr};"
    | .Maximize expr => s!"solve maximize {expr};"

  -- Combine everything
  let allLines := includes ++ [""] ++ varDecls ++ [""] ++ constraints ++ ["", solveStmt]
  String.intercalate "\n" allLines

-- ============================================================================
-- Utility Functions (for analysis and debugging)
-- ============================================================================

/-- Extract variable bounds for MiniZinc variable declarations -/
def extractVariableBoundsForMiniZinc (csp : IntCSP) :
    Fin csp.num_vars → (ℤ × ℤ) :=
  csp.extractAllBounds

/-- Extract all variable bounds as a list for analysis -/
def getAllVariableBounds (csp : IntCSP) : List (ℕ × ℤ × ℤ) :=
  List.ofFn fun (i : Fin csp.num_vars) =>
    let bounds := extractVariableBoundsForMiniZinc csp i
    (i.val, bounds.1, bounds.2)

/-- Check if any variables have default bounds (indicating unbounded variables) -/
def hasDefaultBounds (csp : IntCSP) : Bool :=
  let bounds := getAllVariableBounds csp
  bounds.any fun (_, lb, ub) => lb = -1000 ∧ ub = 1000

/-- Generate statistics about variable bounds for debugging -/
def generateBoundsReport (csp : IntCSP) : String :=
  let bounds := getAllVariableBounds csp
  let lines := bounds.map fun (i, lb, ub) => s!"x{i}: [{lb}, {ub}]"
  let hasDefaults := if hasDefaultBounds csp then
    "⚠️ Some variables use default bounds [-1000, 1000]"
  else
    "✓ All variables have explicit bounds"
  String.intercalate "\n" (hasDefaults :: lines)

/-- Count constraints by type (for analysis) -/
def countConstraintsByType (csp : IntCSP) : String :=
  let patterns := csp.constraints
  let counts := patterns.foldl (fun acc p =>
    let key := match p with
      | IntConstraint.alldifferent _ => "alldifferent"
      | IntConstraint.alldifferentOffset _ _ => "alldifferent_offset"
      | IntConstraint.increasing _ => "increasing"
      | IntConstraint.sum _ _ _ => "sum"
      | IntConstraint.linear _ _ _ _ => "linear"
      | IntConstraint.count _ _ _ => "count"
      | IntConstraint.count_var _ _ _ => "count_var"
      | IntConstraint.element _ _ _ => "element"
      | IntConstraint.maximum _ _ => "maximum"
      | IntConstraint.minimum _ _ => "minimum"
      | IntConstraint.bound _ _ _ => "bound"
      | IntConstraint.eq _ _ => "eq"
      | IntConstraint.ne _ _ => "ne"
      | IntConstraint.lt _ _ => "lt"
      | IntConstraint.le _ _ => "le"
      | IntConstraint.gt _ _ => "gt"
      | IntConstraint.ge _ _ => "ge"
      | IntConstraint.eq_const _ _ => "eq_const"
      | IntConstraint.ne_const _ _ => "ne_const"
      | IntConstraint.lt_const _ _ => "lt_const"
      | IntConstraint.le_const _ _ => "le_const"
      | IntConstraint.gt_const _ _ => "gt_const"
      | IntConstraint.ge_const _ _ => "ge_const"
      | IntConstraint.schur_triple _ _ _ => "schur_triple"
      | IntConstraint.abs_diff_rel _ _ _ _ => "abs_diff_rel"
      | IntConstraint.abs_diff_var _ _ _ => "abs_diff_var"
      | IntConstraint.modulo _ _ _ => "modulo"
      | IntConstraint.sliding_sum _ _ _ _ => "sliding_sum"
      | IntConstraint.not_gate _ _ => "not_gate"
      | IntConstraint.and_gate _ _ _ => "and_gate"
      | IntConstraint.or_gate _ _ _ => "or_gate"
      | IntConstraint.xor_gate _ _ _ => "xor_gate"
      | IntConstraint.nand_gate _ _ _ => "nand_gate"
      | IntConstraint.nor_gate _ _ _ => "nor_gate"
      | IntConstraint.and_all _ _ => "and_all"
      | IntConstraint.or_all _ _ => "or_all"
      | IntConstraint.xor_all _ _ => "xor_all"
      | IntConstraint.implies _ _ => "implies"
      | IntConstraint.iff _ _ => "iff"
      | IntConstraint.if_then _ _ _ _ => "if_then"
      | IntConstraint.if_then_or _ _ _ _ => "if_then_or"
      | IntConstraint.at_least_k _ _ => "at_least_k"
      | IntConstraint.at_most_k _ _ => "at_most_k"
      | IntConstraint.exactly_k _ _ => "exactly_k"
      | IntConstraint.sum_rel_var _ _ _ => "sum_rel_var"
      | IntConstraint.linear_rel_var _ _ _ _ => "linear_rel_var"
      | IntConstraint.product_rel_var _ _ _ => "product_rel_var"
      | IntConstraint.value_precedence _ => "value_precedence"
      | IntConstraint.disjunctive _ _ => "disjunctive"
      | IntConstraint.unknown _ _ => "unknown"
    match acc.find? key with
    | some n => acc.insert key (n + 1)
    | none => acc.insert key 1
  ) (Lean.RBMap.empty : Lean.RBMap String ℕ compare)

  let lines := counts.fold (fun acc key count => s!"{key}: {count}" :: acc) []
  String.intercalate "\n" lines.reverse

end CSP.L2S

namespace CSP.L2S.Z3


open CSP.L2S

/-- Translate to SMT-LIB using old API -/
def translateToSMTLIB (csp : IntCSP) : String :=
  translateTo csp BackendType.SMTLIB

/-- SMT-LIB translation with custom logic -/
def translateToSMTLIBWithLogic (csp : IntCSP) (logic : String) : String :=
  translateTo csp BackendType.SMTLIB { smtLogic := some logic }

end CSP.L2S.Z3
