import CSP.L2S.Core

namespace CSP.L2S

/-!
# Backend Abstraction for Translators

Unified interface for translating IntCSP to various solver formats.

## Design Principles
- Backend selected at runtime (not typeclass inference)
- Error handling with Except for unsupported constraints
- Options for strict mode, logic selection, etc.
- Zero impact on semantic proofs

## Architecture

The backend system provides a common driver (`translateWith`) that handles:
1. Variable declarations
2. Domain assertions
3. Constraint translation loop
4. File assembly (header + decls + constraints + footer)

Each backend only needs to implement:
- Format-specific syntax (MiniZinc vs SMT-LIB)
- Pattern translation logic
- Include/header generation
-/

/-- Translation errors -/
structure TranslatorError where
  msg : String
deriving Repr, Inhabited

/-- Backend-specific options -/
structure BackendOptions where
  /-- Strict mode: error on unsupported constraints vs. emit comments -/
  strict : Bool := false
  /-- SMT-LIB specific: override logic (e.g., "QF_LIA", "QF_NIA") -/
  smtLogic : Option String := none
  /-- SMT-LIB specific: infer logic from constraints -/
  inferLogic : Bool := true
deriving Repr

/-- Default options with proper field defaults -/
instance : Inhabited BackendOptions where
  default := {
    strict := false
    smtLogic := none
    inferLogic := true  -- Correctly use the field default
  }

/-- Backend interface for solver translation -/
structure Backend where
  /-- Backend name (e.g., "MiniZinc", "SMT-LIB") -/
  name : String

  /-- Generate file header (logic declaration, includes, etc.) -/
  header : (csp : IntCSP) → BackendOptions → List String

  /-- Generate file footer (solve statement, check-sat, etc.) -/
  footer : (csp : IntCSP) → BackendOptions → List String

  /-- Generate variable declarations -/
  varDecls : (csp : IntCSP) →
             (Fin csp.num_vars → (ℤ × ℤ)) →
             List String

  /-- Generate domain assertions (separate from declarations) -/
  domainAsserts : (csp : IntCSP) →
                  (Fin csp.num_vars → (ℤ × ℤ)) →
                  List String

  /-- Translate a constraint pattern -/
  translatePattern : {n : ℕ} →
                     BackendOptions →
                     IntConstraint n →
                     Except TranslatorError (List String)

  /-- Should this pattern be skipped in constraint section? -/
  skipInConstraints : {n : ℕ} → IntConstraint n → Bool

/-- Unified translation driver -/
def translateWith (backend : Backend) (opts : BackendOptions)
    (csp : IntCSP) : Except TranslatorError String := do
  -- Extract bounds
  let bounds := csp.extractAllBounds

  -- Generate components
  let header := backend.header csp opts
  let decls := backend.varDecls csp bounds
  let domains := backend.domainAsserts csp bounds
  let footer := backend.footer csp opts

  -- Translate constraints
  let mut constraints : List String := []
  for tc in csp.constraints do
    if backend.skipInConstraints tc then
      continue
    match backend.translatePattern opts tc with
    | .ok lines => constraints := constraints ++ lines
    | .error e =>
        if opts.strict then
          throw e
        else
          -- Non-strict: emit comment and continue
          let comment := match backend.name with
            | "MiniZinc" => s!"% {e.msg}"
            | "SMT-LIB" => s!"; {e.msg}"
            | _ => s!"# {e.msg}"
          constraints := constraints ++ [comment]

  -- Assemble
  let allLines := header ++ decls ++ domains ++ constraints ++ footer
  return String.intercalate "\n" allLines

-- ============================================================================
-- Backend Type Enumeration
-- ============================================================================

/-!
## Backend Types

Enumeration of supported backend types. The actual backend selection and
translation functions are in `CSP.Backends.Translate` to avoid circular dependencies.
-/

/-- Supported backend types for CSP translation -/
inductive BackendType where
  | MiniZinc  -- Constraint programming (MiniZinc solver)
  | SMTLIB    -- SMT solving (Z3, CVC5, etc.)
  deriving Repr, DecidableEq, Inhabited

/-- Get file extension for a backend type -/
def getBackendExtension : BackendType → String
  | BackendType.MiniZinc => "mzn"
  | BackendType.SMTLIB => "smt2"

/-- Get output directory name for a backend type -/
def getBackendDirName : BackendType → String
  | BackendType.MiniZinc => "mzn"
  | BackendType.SMTLIB => "smt2"

/-- Get human-readable name for a backend type -/
def getBackendName : BackendType → String
  | BackendType.MiniZinc => "MiniZinc"
  | BackendType.SMTLIB => "SMT-LIB"

/-- List all available backends -/
def allBackends : List BackendType :=
  [BackendType.MiniZinc, BackendType.SMTLIB]

end CSP.L2S
