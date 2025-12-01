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

def translateToExcept (csp : HomogeneousCSP)
                      (backendType : BackendType)
                      (opts : BackendOptions := default)
                      : Except TranslatorError String :=
  translateWith (selectBackend backendType) opts csp


def translateTo (csp : HomogeneousCSP)
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
def saveTo (csp : HomogeneousCSP)
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
def saveToAuto (csp : HomogeneousCSP)
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


def translateToMiniZinc (csp : HomogeneousCSP) : String :=
  translateTo csp BackendType.MiniZinc

/-- Solving objectives for MiniZinc optimization problems -/
inductive SolveObjective where
  | Satisfy
  | Minimize (expr : String)
  | Maximize (expr : String)
  deriving Repr

/-- MiniZinc translation with custom objective -/
def translateToMiniZincWithObjective (csp : HomogeneousCSP)
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
    match tc.pattern with
    | ConstraintPattern.bound _ _ _ => none
    | _ =>
        match MiniZinc.patternToMiniZinc default tc.pattern with
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
def extractVariableBoundsForMiniZinc (csp : HomogeneousCSP) :
    Fin csp.num_vars → (ℤ × ℤ) :=
  csp.extractAllBounds

/-- Extract all variable bounds as a list for analysis -/
def getAllVariableBounds (csp : HomogeneousCSP) : List (ℕ × ℤ × ℤ) :=
  List.ofFn fun (i : Fin csp.num_vars) =>
    let bounds := extractVariableBoundsForMiniZinc csp i
    (i.val, bounds.1, bounds.2)

/-- Check if any variables have default bounds (indicating unbounded variables) -/
def hasDefaultBounds (csp : HomogeneousCSP) : Bool :=
  let bounds := getAllVariableBounds csp
  bounds.any fun (_, lb, ub) => lb = -1000 ∧ ub = 1000

/-- Generate statistics about variable bounds for debugging -/
def generateBoundsReport (csp : HomogeneousCSP) : String :=
  let bounds := getAllVariableBounds csp
  let lines := bounds.map fun (i, lb, ub) => s!"x{i}: [{lb}, {ub}]"
  let hasDefaults := if hasDefaultBounds csp then
    "⚠️ Some variables use default bounds [-1000, 1000]"
  else
    "✓ All variables have explicit bounds"
  String.intercalate "\n" (hasDefaults :: lines)

/-- Count constraints by type (for analysis) -/
def countConstraintsByType (csp : HomogeneousCSP) : String :=
  let patterns := csp.constraints.map (·.pattern)
  let counts := patterns.foldl (fun acc p =>
    let key := match p with
      | ConstraintPattern.alldifferent _ => "alldifferent"
      | ConstraintPattern.alldifferentOffset _ _ => "alldifferent_offset"
      | ConstraintPattern.increasing _ => "increasing"
      | ConstraintPattern.sum _ _ _ => "sum"
      | ConstraintPattern.linear _ _ _ _ => "linear"
      | ConstraintPattern.count _ _ _ => "count"
      | ConstraintPattern.count_var _ _ _ => "count_var"
      | ConstraintPattern.element _ _ _ => "element"
      | ConstraintPattern.maximum _ _ => "maximum"
      | ConstraintPattern.minimum _ _ => "minimum"
      | ConstraintPattern.bound _ _ _ => "bound"
      | ConstraintPattern.eq _ _ => "eq"
      | ConstraintPattern.ne _ _ => "ne"
      | ConstraintPattern.lt _ _ => "lt"
      | ConstraintPattern.le _ _ => "le"
      | ConstraintPattern.gt _ _ => "gt"
      | ConstraintPattern.ge _ _ => "ge"
      | ConstraintPattern.eq_const _ _ => "eq_const"
      | ConstraintPattern.ne_const _ _ => "ne_const"
      | ConstraintPattern.lt_const _ _ => "lt_const"
      | ConstraintPattern.le_const _ _ => "le_const"
      | ConstraintPattern.gt_const _ _ => "gt_const"
      | ConstraintPattern.ge_const _ _ => "ge_const"
      | ConstraintPattern.schur_triple _ _ _ => "schur_triple"
      | ConstraintPattern.abs_diff_rel _ _ _ _ => "abs_diff_rel"
      | ConstraintPattern.abs_diff_var _ _ _ => "abs_diff_var"
      | ConstraintPattern.modulo _ _ _ => "modulo"
      | ConstraintPattern.sliding_sum _ _ _ _ => "sliding_sum"
      | ConstraintPattern.not_gate _ _ => "not_gate"
      | ConstraintPattern.and_gate _ _ _ => "and_gate"
      | ConstraintPattern.or_gate _ _ _ => "or_gate"
      | ConstraintPattern.xor_gate _ _ _ => "xor_gate"
      | ConstraintPattern.nand_gate _ _ _ => "nand_gate"
      | ConstraintPattern.nor_gate _ _ _ => "nor_gate"
      | ConstraintPattern.and_all _ _ => "and_all"
      | ConstraintPattern.or_all _ _ => "or_all"
      | ConstraintPattern.xor_all _ _ => "xor_all"
      | ConstraintPattern.implies _ _ => "implies"
      | ConstraintPattern.iff _ _ => "iff"
      | ConstraintPattern.if_then _ _ _ _ => "if_then"
      | ConstraintPattern.if_then_or _ _ _ _ => "if_then_or"
      | ConstraintPattern.at_least_k _ _ => "at_least_k"
      | ConstraintPattern.at_most_k _ _ => "at_most_k"
      | ConstraintPattern.exactly_k _ _ => "exactly_k"
      | ConstraintPattern.sum_rel_var _ _ _ => "sum_rel_var"
      | ConstraintPattern.linear_rel_var _ _ _ _ => "linear_rel_var"
      | ConstraintPattern.product_rel_var _ _ _ => "product_rel_var"
      | ConstraintPattern.disjunctive _ _ => "disjunctive"
      | ConstraintPattern.unknown _ _ => "unknown"
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
def translateToSMTLIB (csp : HomogeneousCSP) : String :=
  translateTo csp BackendType.SMTLIB

/-- SMT-LIB translation with custom logic -/
def translateToSMTLIBWithLogic (csp : HomogeneousCSP) (logic : String) : String :=
  translateTo csp BackendType.SMTLIB { smtLogic := some logic }

end CSP.L2S.Z3
