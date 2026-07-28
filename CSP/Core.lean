import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Mem
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Basic

namespace CSP

set_option linter.dupNamespace false

open Vector

/-! ### Type-safe heterogeneous operations with fixed-length vectors -/

/-- Values matching a scope: dependent function over vector indices -/
def ScopeValues (VarIndex : Type) (DomainType : VarIndex → Type)
    (scope : Vector VarIndex n) : Type :=
  (i : Fin n) → DomainType (scope.get i)

/-! ### Core CSP Definitions with Heterogeneous Domains -/

/-- Helper for Bool to Prop conversion -/
@[simp] def sat (b : Bool) : Prop := b = true

/-- A constraint with fixed arity, scope vector, and Boolean check function -/
structure Constraint (VarIndex : Type) (DomainType : VarIndex → Type) (n : ℕ) where
  scope : Vector VarIndex n
  check : ScopeValues VarIndex DomainType scope → Bool

/-- Dynamic constraint wrapper for constraints of different arities -/
inductive DynamicConstraint (VarIndex : Type) (DomainType : VarIndex → Type) where
  | mk : (n : ℕ) → Constraint VarIndex DomainType n → DynamicConstraint VarIndex DomainType

/-- Assignment is a dependent function mapping each variable to a value of its domain type -/
abbrev Assignment (VarIndex : Type) (DomainType : VarIndex → Type) :=
  (v : VarIndex) → DomainType v

/-- Map an assignment to scope values for the given vector scope -/
def map_assignment {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (assignment : Assignment VarIndex DomainType)
    (scope : Vector VarIndex n) : ScopeValues VarIndex DomainType scope :=
  fun i => assignment (scope.get i)

/-- Check if an assignment satisfies a fixed-arity constraint -/
def satisfies_constraint {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (c : Constraint VarIndex DomainType n)
    (assignment : Assignment VarIndex DomainType) : Prop :=
  sat (c.check (map_assignment assignment c.scope))

/-- Check if an assignment satisfies a dynamic constraint -/
def satisfies_dynamic_constraint {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (dc : DynamicConstraint VarIndex DomainType)
    (assignment : Assignment VarIndex DomainType) : Prop :=
  match dc with
  | DynamicConstraint.mk _ c => satisfies_constraint c assignment

/-- A CSP with heterogeneous domains and dynamic constraints -/
structure CSP (VarIndex : Type) (DomainType : VarIndex → Type) where
  domain : (v : VarIndex) → Set (DomainType v)
  constraints : List (DynamicConstraint VarIndex DomainType)

/-- An assignment is valid if it respects domain restrictions for each variable -/
def valid_assignment {VarIndex : Type} {DomainType : VarIndex → Type}
    (csp : CSP VarIndex DomainType)
    (assignment : Assignment VarIndex DomainType) : Prop :=
  ∀ v : VarIndex, assignment v ∈ csp.domain v

/-- An assignment is a solution if it's valid and satisfies all constraints -/
def is_solution {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType)
    (assignment : Assignment VarIndex DomainType) : Prop :=
  valid_assignment csp assignment ∧
  ∀ c ∈ csp.constraints, satisfies_dynamic_constraint c assignment

/-- A CSP is satisfiable if it has at least one solution -/
def is_satisfiable {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) : Prop :=
  ∃ assignment, is_solution csp assignment

/-! ### Bool/Prop Bridge Lemmas -/

section BoolPropBridge

@[simp] lemma sat_iff {b : Bool} : sat b ↔ b = true := Iff.rfl

@[simp] lemma sat_and {a b : Bool} : sat (a && b) ↔ sat a ∧ sat b := by
  simp [sat]

@[simp] lemma sat_or {a b : Bool} : sat (a || b) ↔ sat a ∨ sat b := by
  simp [sat]

@[simp] lemma sat_not {b : Bool} : sat (!b) ↔ ¬sat b := by
  simp [sat]

end BoolPropBridge

/-! ### Decidability Instances -/

section Decidability

/-- Decidability instance for constraint satisfaction -/
instance decidable_satisfies_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    [DecidableEq VarIndex] (c : Constraint VarIndex DomainType n) (assignment : Assignment VarIndex DomainType) :
    Decidable (satisfies_constraint c assignment) := by
  simp only [satisfies_constraint, sat]
  infer_instance

/-- Decidability instance for dynamic constraint satisfaction -/
instance decidable_satisfies_dynamic_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    [DecidableEq VarIndex] (dc : DynamicConstraint VarIndex DomainType) (assignment : Assignment VarIndex DomainType) :
    Decidable (satisfies_dynamic_constraint dc assignment) := by
  cases dc with
  | mk n c => exact decidable_satisfies_constraint c assignment

end Decidability

/-! ### Constraint Constructors for Heterogeneous Domains -/

section ConstraintConstructors

/-- Create a unary constraint on a single variable -/
def unary_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (v : VarIndex) (p : DomainType v → Bool) : Constraint VarIndex DomainType 1 where
  scope := ⟨#[v], rfl⟩
  check := fun values => p (values ⟨0, by simp⟩)

/-- Create a binary constraint on two variables (can be of different types) -/
def binary_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (v1 v2 : VarIndex) (p : DomainType v1 → DomainType v2 → Bool) : Constraint VarIndex DomainType 2 where
  scope := ⟨#[v1, v2], rfl⟩
  check := fun values => p (values ⟨0, by simp⟩) (values ⟨1, by simp⟩)

/-- Create a ternary constraint on three variables (can be of different types) -/
def ternary_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (v1 v2 v3 : VarIndex) (p : DomainType v1 → DomainType v2 → DomainType v3 → Bool) :
    Constraint VarIndex DomainType 3 where
  scope := ⟨#[v1, v2, v3], rfl⟩
  check := fun values => p (values ⟨0, by simp⟩) (values ⟨1, by simp⟩) (values ⟨2, by simp⟩)

/-- Create an n-ary constraint with explicit scope vector -/
def nary_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (scope : Vector VarIndex n) (p : ScopeValues VarIndex DomainType scope → Bool) :
    Constraint VarIndex DomainType n where
  scope := scope
  check := p

/-- Create a dynamic unary constraint -/
def unary_dynamic_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (v : VarIndex) (p : DomainType v → Bool) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk 1 (unary_constraint v p)

/-- Create a dynamic binary constraint -/
def binary_dynamic_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (v1 v2 : VarIndex) (p : DomainType v1 → DomainType v2 → Bool) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk 2 (binary_constraint v1 v2 p)

/-- Create a dynamic ternary constraint -/
def ternary_dynamic_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (v1 v2 v3 : VarIndex) (p : DomainType v1 → DomainType v2 → DomainType v3 → Bool) :
    DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk 3 (ternary_constraint v1 v2 v3 p)

/-- Create a dynamic n-ary constraint -/
def nary_dynamic_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (scope : Vector VarIndex n) (p : ScopeValues VarIndex DomainType scope → Bool) :
    DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk n (nary_constraint scope p)

/-- Create an empty CSP with no constraints -/
def empty_csp {VarIndex : Type} {DomainType : VarIndex → Type}
    (domain : (v : VarIndex) → Set (DomainType v)) : CSP VarIndex DomainType where
  domain := domain
  constraints := []

/-- Add a single dynamic constraint to a CSP -/
def add_constraint {VarIndex : Type} {DomainType : VarIndex → Type}
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) :
    CSP VarIndex DomainType :=
  ⟨csp.domain, c :: csp.constraints⟩

/-- Add multiple dynamic constraints to a CSP -/
def add_constraints {VarIndex : Type} {DomainType : VarIndex → Type}
    (csp : CSP VarIndex DomainType) (cs : List (DynamicConstraint VarIndex DomainType)) :
    CSP VarIndex DomainType :=
  ⟨csp.domain, cs ++ csp.constraints⟩

end ConstraintConstructors

/-! ### Utility Functions -/

section UtilityFunctions

/-- Check if a variable appears in a constraint's scope -/
def constraint_uses_var {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (c : Constraint VarIndex DomainType n) (v : VarIndex) : Bool :=
  decide (v ∈ c.scope.toList)


/-- Check if a variable appears in a dynamic constraint's scope -/
def dynamic_constraint_uses_var {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (dc : DynamicConstraint VarIndex DomainType) (v : VarIndex) : Bool :=
  match dc with
  | DynamicConstraint.mk _ c => constraint_uses_var c v

/-- Get all variables used in a CSP -/
def csp_variables {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) : List VarIndex :=
  (csp.constraints.map (fun dc => match dc with
    | DynamicConstraint.mk _ c => c.scope.toList)).flatten.eraseDup

/-- Count constraints in a CSP -/
def constraint_count {VarIndex : Type} {DomainType : VarIndex → Type}
    (csp : CSP VarIndex DomainType) : ℕ :=
  csp.constraints.length

/-- Check if assignment satisfies all constraints (without domain check) -/
def satisfies_all_constraints {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (assignment : Assignment VarIndex DomainType) : Prop :=
  ∀ c ∈ csp.constraints, satisfies_dynamic_constraint c assignment

end UtilityFunctions

/-! ### Key Lemmas for Vector-based Operations -/

section VectorLemmas

/-- Map assignment get lemma for vectors -/
@[simp]
lemma map_assignment_get {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {assignment : Assignment VarIndex DomainType} {scope : Vector VarIndex n} {i : Fin n} :
    (map_assignment assignment scope) i = assignment (scope.get i) := by
  simp only [map_assignment]

/-- Extensionality for scope values -/
lemma scope_values_ext {VarIndex : Type} {DomainType : VarIndex → Type}
    {scope : Vector VarIndex n} {v1 v2 : ScopeValues VarIndex DomainType scope}
    (h : ∀ i, v1 i = v2 i) : v1 = v2 :=
  funext h

/-- Constraint satisfaction is preserved under equivalent assignments -/
lemma satisfies_constraint_of_eq {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {c : Constraint VarIndex DomainType n} {a1 a2 : Assignment VarIndex DomainType}
    (h : ∀ v ∈ c.scope.toList, a1 v = a2 v) :
    satisfies_constraint c a1 ↔ satisfies_constraint c a2 := by
  simp only [satisfies_constraint]
  have h_eq : c.check (map_assignment a1 c.scope) = c.check (map_assignment a2 c.scope) := by
    congr 1
    apply scope_values_ext
    intro i
    simp only [map_assignment]
    apply h
    exact List.mem_of_getElem rfl
  rw [h_eq]

end VectorLemmas

end CSP
