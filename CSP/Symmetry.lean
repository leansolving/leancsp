import CSP.Core
import CSP.Equivalence
import Mathlib.Logic.Equiv.Basic

namespace CSP

open Equiv

/-! ### Extended CSP for Symmetry Breaking -/

section ExtendedCSP

/-- Extended CSP for symmetry breaking - adds a dynamic constraint to an existing CSP -/
def extended_csp {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) : CSP VarIndex DomainType :=
  c :: csp

/-- Solutions of an extended CSP are solutions of the original -/
theorem extended_csp_satisfiable_implies_satisfiable
    {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) :
    is_satisfiable (extended_csp csp c) → is_satisfiable csp := by
  intro ⟨assignment, h_sol⟩
  exact ⟨assignment, fun constraint hc => h_sol constraint (List.mem_cons_of_mem c hc)⟩

end ExtendedCSP

/-! ### Domain Equivalence Families -/

/-- A domain equivalence family provides an equivalence for each variable's domain type.
    This generalizes the homogeneous case where all variables shared the same domain. -/
def DomainEquivFamily (VarIndex : Type) (DomainType : VarIndex → Type) : Type :=
  (v : VarIndex) → Equiv (DomainType v) (DomainType v)

namespace DomainEquivFamily

/-- Extensionality for domain equivalence families -/
@[ext]
theorem ext {VarIndex : Type} {DomainType : VarIndex → Type}
    {δ₁ δ₂ : DomainEquivFamily VarIndex DomainType}
    (h : ∀ v, δ₁ v = δ₂ v) : δ₁ = δ₂ :=
  funext h

/-- Apply a domain equivalence family to an assignment -/
def apply {VarIndex : Type} {DomainType : VarIndex → Type}
    (δ : DomainEquivFamily VarIndex DomainType)
    (assignment : Assignment VarIndex DomainType) : Assignment VarIndex DomainType :=
  fun v => (δ v) (assignment v)

end DomainEquivFamily

/-! ### Solution-Level Symmetries -/

/-- Type compatibility for a variable permutation: permuting variable indices
    preserves domain types -/
def DomainTypePreserving {VarIndex : Type} {DomainType : VarIndex → Type}
    (β : Equiv VarIndex VarIndex) : Prop :=
  ∀ v : VarIndex, DomainType (β v) = DomainType v

/-- Apply a variable permutation to an assignment, casting along type compatibility -/
def applyVariablePerm {VarIndex : Type} {DomainType : VarIndex → Type}
    (β : Equiv VarIndex VarIndex) (assignment : Assignment VarIndex DomainType)
    (h_types : ∀ v : VarIndex, DomainType (β v) = DomainType v) : Assignment VarIndex DomainType :=
  fun v => cast (h_types v) (assignment (β v))

/-- A domain symmetry is a domain equivalence family that preserves all solutions -/
def DomainSymmetry {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (δ : DomainEquivFamily VarIndex DomainType) : Prop :=
  ∀ assignment, is_solution csp assignment → is_solution csp (δ.apply assignment)

/-- A variable symmetry is a type-compatible variable permutation that preserves
    all solutions -/
def VariableSymmetry {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (β : Equiv VarIndex VarIndex)
    (h_types : DomainTypePreserving (DomainType := DomainType) β) : Prop :=
  ∀ assignment, is_solution csp assignment →
    is_solution csp (applyVariablePerm β assignment h_types)

/-! ### Symmetry Breaking Constraints -/

/-- A constraint is a domain symmetry breaking constraint if for every solution
    of the original CSP, there exists a domain symmetry that transforms it into
    a solution of the extended CSP -/
def domainSymmetryBreakingConstraint {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) : Prop :=
  ∀ assignment : Assignment VarIndex DomainType, is_solution csp assignment →
    ∃ δ : DomainEquivFamily VarIndex DomainType,
      DomainSymmetry csp δ ∧
      is_solution (extended_csp csp c) (δ.apply assignment)

/-- Domain symmetry breaking constraints preserve equisatisfiability -/
theorem domainSymmetryBreaking_equisatisfiability
    {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType)
    (h_sbc : domainSymmetryBreakingConstraint csp c) :
    equisatisfiable csp (extended_csp csp c) := by
  constructor
  · intro ⟨assignment, h_sol⟩
    obtain ⟨δ, _, h_ext_sol⟩ := h_sbc assignment h_sol
    exact ⟨δ.apply assignment, h_ext_sol⟩
  · exact extended_csp_satisfiable_implies_satisfiable csp c

/-- A constraint is a variable symmetry breaking constraint if for every solution
    of the original CSP, there exists a variable symmetry that transforms it into
    a solution of the extended CSP -/
def variableSymmetryBreakingConstraint {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) : Prop :=
  ∀ assignment : Assignment VarIndex DomainType, is_solution csp assignment →
    ∃ β : Equiv VarIndex VarIndex,
      ∃ h_types : DomainTypePreserving (DomainType := DomainType) β,
        VariableSymmetry csp β h_types ∧
        is_solution (extended_csp csp c) (applyVariablePerm β assignment h_types)

/-- Variable symmetry breaking constraints preserve equisatisfiability -/
theorem variableSymmetryBreaking_equisatisfiability
    {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType)
    (h_sbc : variableSymmetryBreakingConstraint csp c) :
    equisatisfiable csp (extended_csp csp c) := by
  constructor
  · intro ⟨assignment, h_sol⟩
    obtain ⟨β, h_types, _, h_ext_sol⟩ := h_sbc assignment h_sol
    exact ⟨applyVariablePerm β assignment h_types, h_ext_sol⟩
  · exact extended_csp_satisfiable_implies_satisfiable csp c

/-! ### Constraint Symmetries -/

/-- Apply a domain equivalence family to scope values by applying the appropriate
    equivalence for each variable in the scope -/
def apply_equiv_to_scope_values {VarIndex : Type} {DomainType : VarIndex → Type}
    (δ : DomainEquivFamily VarIndex DomainType)
    (scope : Vector VarIndex n) (values : ScopeValues VarIndex DomainType scope) :
    ScopeValues VarIndex DomainType scope :=
  fun i => (δ (scope.get i)) (values i)

/-- A constraint is symmetric with respect to a domain equivalence family if its
    check function is invariant under applying the equivalences to the scope values -/
def constraint_domain_symmetric {VarIndex : Type} {DomainType : VarIndex → Type}
    (c : Constraint VarIndex DomainType n) (δ : DomainEquivFamily VarIndex DomainType) : Prop :=
  ∀ (values : ScopeValues VarIndex DomainType c.scope),
    c.check (apply_equiv_to_scope_values δ c.scope values) = c.check values

/-- A dynamic constraint is symmetric with respect to a domain equivalence family -/
def dynamic_constraint_domain_symmetric {VarIndex : Type} {DomainType : VarIndex → Type}
    (dc : DynamicConstraint VarIndex DomainType) (δ : DomainEquivFamily VarIndex DomainType) : Prop :=
  match dc with
  | DynamicConstraint.mk _ c => constraint_domain_symmetric c δ

/-- A constraint is symmetric with respect to a variable permutation if applying
    the permutation to the scope preserves the constraint evaluation -/
def constraint_variable_symmetric {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (c : Constraint VarIndex DomainType n) (β : Equiv VarIndex VarIndex)
    (h_types : ∀ v : VarIndex, DomainType (β v) = DomainType v) : Prop :=
  ∀ (assignment : Assignment VarIndex DomainType),
    satisfies_constraint c (applyVariablePerm β assignment h_types) = satisfies_constraint c assignment

/-- A dynamic constraint is symmetric with respect to a variable permutation -/
def dynamic_constraint_variable_symmetric {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (dc : DynamicConstraint VarIndex DomainType) (β : Equiv VarIndex VarIndex)
    (h_types : ∀ v : VarIndex, DomainType (β v) = DomainType v) : Prop :=
  match dc with
  | DynamicConstraint.mk _ c => constraint_variable_symmetric c β h_types

section AssignmentLemmas

/-- Map assignment commutes with domain equivalence application -/
@[simp]
lemma map_assignment_apply_equiv {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {assignment : Assignment VarIndex DomainType} {scope : Vector VarIndex n}
    {δ : DomainEquivFamily VarIndex DomainType} :
    map_assignment (δ.apply assignment) scope =
    apply_equiv_to_scope_values δ scope (map_assignment assignment scope) := by
  apply scope_values_ext
  intro i
  simp only [map_assignment, apply_equiv_to_scope_values, DomainEquivFamily.apply]

end AssignmentLemmas

/-! ### Symmetry Preservation Theorems -/

/-- Domain symmetry preserves constraint satisfaction -/
theorem constraint_symmetric_preserves_satisfaction {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {c : Constraint VarIndex DomainType n} {δ : DomainEquivFamily VarIndex DomainType}
    (h_symm : constraint_domain_symmetric c δ)
    (assignment : Assignment VarIndex DomainType) :
    satisfies_constraint c (δ.apply assignment) ↔ satisfies_constraint c assignment := by
  simp only [satisfies_constraint, sat_iff]
  rw [map_assignment_apply_equiv]
  rw [h_symm]

/-- Domain symmetry preserves dynamic constraint satisfaction -/
theorem dynamic_constraint_symmetric_preserves_satisfaction {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {dc : DynamicConstraint VarIndex DomainType} {δ : DomainEquivFamily VarIndex DomainType}
    (h_symm : dynamic_constraint_domain_symmetric dc δ)
    (assignment : Assignment VarIndex DomainType) :
    satisfies_dynamic_constraint dc (δ.apply assignment) ↔ satisfies_dynamic_constraint dc assignment := by
  cases dc with
  | mk n c =>
    simp only [satisfies_dynamic_constraint, dynamic_constraint_domain_symmetric] at h_symm ⊢
    exact constraint_symmetric_preserves_satisfaction h_symm assignment

/-- Constraint-wise invariance is sufficient for a domain symmetry -/
theorem domain_symmetry_preserves_solutions {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (δ : DomainEquivFamily VarIndex DomainType)
    (h_constraints : ∀ c ∈ csp, dynamic_constraint_domain_symmetric c δ) :
    DomainSymmetry csp δ := by
  intro assignment h_sat c hc
  rw [dynamic_constraint_symmetric_preserves_satisfaction (h_constraints c hc)]
  exact h_sat c hc

/-- Constraint-wise invariance is sufficient for a variable symmetry -/
theorem variable_symmetry_preserves_solutions {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (β : Equiv VarIndex VarIndex)
    (h_types : DomainTypePreserving (DomainType := DomainType) β)
    (h_constraints : ∀ c ∈ csp, dynamic_constraint_variable_symmetric c β h_types) :
    VariableSymmetry csp β h_types := by
  intro assignment h_sat c hc
  have h_constraint_sym := h_constraints c hc
  cases c with
  | mk n constraint =>
    simp only [satisfies_dynamic_constraint] at h_constraint_sym ⊢
    rw [h_constraint_sym]
    exact h_sat (DynamicConstraint.mk n constraint) hc

end CSP
