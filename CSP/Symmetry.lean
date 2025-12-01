import CSP.Core
import CSP.Equivalence
import CSP.Transport
import Mathlib.Logic.Equiv.Basic

namespace CSP

open Equiv

-- ============================================================================
-- Extended CSP for Symmetry Breaking
-- ============================================================================

section ExtendedCSP

/-- Extended CSP for symmetry breaking - adds a dynamic constraint to an existing CSP -/
def extended_csp {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) : CSP VarIndex DomainType :=
  ⟨csp.domain, c :: csp.constraints⟩

end ExtendedCSP

-- ============================================================================
-- Heterogeneous Domain Symmetries
-- ============================================================================

/-- A domain symmetry family provides an equivalence for each variable's domain type.
    This generalizes the homogeneous case where all variables shared the same domain. -/
structure DomainSymmetryFamily (VarIndex : Type) (DomainType : VarIndex → Type) where
  to_equiv : (v : VarIndex) → Equiv (DomainType v) (DomainType v)

namespace DomainSymmetryFamily

/-- Extensionality for domain symmetry families -/
@[ext]
theorem ext {VarIndex : Type} {DomainType : VarIndex → Type}
    {σ₁ σ₂ : DomainSymmetryFamily VarIndex DomainType}
    (h : ∀ v, σ₁.to_equiv v = σ₂.to_equiv v) : σ₁ = σ₂ := by
  cases σ₁ with | mk f₁ =>
  cases σ₂ with | mk f₂ =>
  congr
  funext v
  exact h v

/-- Apply a domain symmetry family to an assignment -/
def apply {VarIndex : Type} {DomainType : VarIndex → Type}
    (σ : DomainSymmetryFamily VarIndex DomainType)
    (assignment : Assignment VarIndex DomainType) : Assignment VarIndex DomainType :=
  fun v => σ.to_equiv v (assignment v)

/-- Convert a domain symmetry family to a permutation on the assignment space -/
def as_perm {VarIndex : Type} {DomainType : VarIndex → Type}
    (σ : DomainSymmetryFamily VarIndex DomainType) :
    Equiv.Perm (Assignment VarIndex DomainType) :=
  Equiv.piCongrRight σ.to_equiv

/-- Identity domain symmetry family -/
def identity {VarIndex : Type} {DomainType : VarIndex → Type} :
    DomainSymmetryFamily VarIndex DomainType where
  to_equiv := fun _ => Equiv.refl _

/-- Composition of domain symmetry families -/
def comp {VarIndex : Type} {DomainType : VarIndex → Type}
    (σ₁ σ₂ : DomainSymmetryFamily VarIndex DomainType) :
    DomainSymmetryFamily VarIndex DomainType where
  to_equiv := fun v => (σ₁.to_equiv v).trans (σ₂.to_equiv v)

/-- Inverse of a domain symmetry family -/
def inv {VarIndex : Type} {DomainType : VarIndex → Type}
    (σ : DomainSymmetryFamily VarIndex DomainType) :
    DomainSymmetryFamily VarIndex DomainType where
  to_equiv := fun v => (σ.to_equiv v).symm

end DomainSymmetryFamily

-- ============================================================================
-- Variable Symmetries for Heterogeneous Domains
-- ============================================================================

/-- A variable symmetry in heterogeneous domains requires domain type preservation.
    This is a very restrictive condition - most useful when domain types are uniform. -/
def variable_symmetry {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (π : Equiv VarIndex VarIndex) : Prop :=
  (∀ v : VarIndex, DomainType (π v) = DomainType v) ∧
  (∀ v : VarIndex, ∀ h : DomainType (π v) = DomainType v,
    @Eq.mpr (Set (DomainType v)) (Set (DomainType (π v))) (congr_arg Set h.symm) (csp.domain (π v)) = csp.domain v)

-- ============================================================================
-- Domain Symmetries for CSPs
-- ============================================================================

/-- A domain symmetry family respects the CSP's domain constraints -/
def domain_symmetry {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (σ : DomainSymmetryFamily VarIndex DomainType) : Prop :=
  ∀ v : VarIndex, ∀ d ∈ csp.domain v, σ.to_equiv v d ∈ csp.domain v

-- ============================================================================
-- Constraint Symmetries with ScopeValues
-- ============================================================================

/-- Apply a domain symmetry family to scope values by applying the appropriate
    symmetry for each variable in the scope -/
def apply_symmetry_to_scope_values {VarIndex : Type} {DomainType : VarIndex → Type}
    (σ : DomainSymmetryFamily VarIndex DomainType)
    (scope : Vector VarIndex n) (values : ScopeValues VarIndex DomainType scope) :
    ScopeValues VarIndex DomainType scope :=
  fun i => σ.to_equiv (scope.get i) (values i)

/-- A constraint is symmetric with respect to a domain symmetry family if its
    check function is invariant under applying the symmetries to the scope values -/
def constraint_domain_symmetric {VarIndex : Type} {DomainType : VarIndex → Type}
    (c : Constraint VarIndex DomainType n) (σ : DomainSymmetryFamily VarIndex DomainType) : Prop :=
  ∀ (values : ScopeValues VarIndex DomainType c.scope),
    c.check (apply_symmetry_to_scope_values σ c.scope values) = c.check values

/-- A dynamic constraint is symmetric with respect to a domain symmetry family -/
def dynamic_constraint_domain_symmetric {VarIndex : Type} {DomainType : VarIndex → Type}
    (dc : DynamicConstraint VarIndex DomainType) (σ : DomainSymmetryFamily VarIndex DomainType) : Prop :=
  match dc with
  | DynamicConstraint.mk _ c => constraint_domain_symmetric c σ

-- ============================================================================
-- Variable Symmetry Preservation and Constraint Symmetries
-- ============================================================================

/-- Apply a variable symmetry to an assignment by permuting variables.
    This requires careful type handling due to the type compatibility requirement. -/
def apply_variable_symmetry {VarIndex : Type} {DomainType : VarIndex → Type}
    (π : Equiv VarIndex VarIndex) (assignment : Assignment VarIndex DomainType)
    (h_types : ∀ v : VarIndex, DomainType (π v) = DomainType v) : Assignment VarIndex DomainType :=
  fun v => cast (h_types v) (assignment (π v))

/-- A constraint is symmetric with respect to a variable permutation if applying
    the permutation to the scope preserves the constraint evaluation -/
def constraint_variable_symmetric {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (c : Constraint VarIndex DomainType n) (π : Equiv VarIndex VarIndex)
    (h_types : ∀ v : VarIndex, DomainType (π v) = DomainType v) : Prop :=
  ∀ (assignment : Assignment VarIndex DomainType),
    satisfies_constraint c (apply_variable_symmetry π assignment h_types) = satisfies_constraint c assignment

/-- A dynamic constraint is symmetric with respect to a variable permutation -/
def dynamic_constraint_variable_symmetric {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (dc : DynamicConstraint VarIndex DomainType) (π : Equiv VarIndex VarIndex)
    (h_types : ∀ v : VarIndex, DomainType (π v) = DomainType v) : Prop :=
  match dc with
  | DynamicConstraint.mk _ c => constraint_variable_symmetric c π h_types

-- ============================================================================
-- Variable Symmetry Preservation Theorems
-- ============================================================================

/-- Variable symmetries preserve solutions when type compatibility holds -/
theorem variable_symmetry_preserves_solutions {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (π : Equiv VarIndex VarIndex)
    (h_var_sym : variable_symmetry csp π)
    (h_constraints : ∀ c ∈ csp.constraints, dynamic_constraint_variable_symmetric c π h_var_sym.1) :
    ∀ assignment : Assignment VarIndex DomainType,
      is_solution csp assignment → is_solution csp (apply_variable_symmetry π assignment h_var_sym.1) := by
  intro assignment ⟨h_valid, h_sat⟩
  constructor
  · intro v
    simp only [apply_variable_symmetry]
    have h_domain_eq := h_var_sym.2 v (h_var_sym.1 v)
    have h_mem : assignment (π v) ∈ csp.domain (π v) := h_valid (π v)
    have h_cast_mem : cast (h_var_sym.1 v) (assignment (π v)) ∈ csp.domain v := by
      rw [← h_domain_eq]
      convert h_mem
      exact mem_cast_iff_mpr_symm (h_var_sym.1 v) (csp.domain (π v)) (assignment (π v))
    exact h_cast_mem
  · intro c hc
    have h_constraint_sym := h_constraints c hc
    cases c with
    | mk n constraint =>
      simp only [satisfies_dynamic_constraint] at h_constraint_sym ⊢
      rw [h_constraint_sym]
      have h_orig := h_sat (DynamicConstraint.mk n constraint) hc
      exact h_orig

-- ============================================================================
-- Variable Symmetry Breaking Constraints
-- ============================================================================

/-- A constraint is a variable symmetry breaking constraint if for every solution
    of the original CSP, there exists a variable symmetry that transforms it into
    a solution of the extended CSP -/
def variable_symmetry_breaking_constraint {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) : Prop :=
  ∀ assignment : Assignment VarIndex DomainType, is_solution csp assignment →
    ∃ π : Equiv VarIndex VarIndex,
      ∃ h_var_sym : variable_symmetry csp π,
        (∀ constraint ∈ csp.constraints, dynamic_constraint_variable_symmetric constraint π h_var_sym.1) ∧
        is_solution (extended_csp csp c) (apply_variable_symmetry π assignment h_var_sym.1)

/-- Variable symmetry breaking constraints preserve equisatisfiability -/
theorem variable_symmetry_breaking_preserves_equisatisfiability
    {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType)
    (h_sbc : variable_symmetry_breaking_constraint csp c) :
    equisatisfiable csp (extended_csp csp c) := by
  constructor
  · -- If original CSP is satisfiable, extended CSP is satisfiable
    intro ⟨assignment, h_sol⟩
    obtain ⟨π, h_var_sym, h_constraint_sym, h_ext_sol⟩ := h_sbc assignment h_sol
    exact ⟨apply_variable_symmetry π assignment h_var_sym.1, h_ext_sol⟩
  · -- If extended CSP is satisfiable, original CSP is satisfiable
    intro ⟨assignment, h_ext_sol⟩
    have h_sol : is_solution csp assignment := by
      constructor
      · exact h_ext_sol.1
      · intro constraint h_constraint
        exact h_ext_sol.2 constraint (List.mem_cons_of_mem c h_constraint)
    exact ⟨assignment, h_sol⟩


-- ============================================================================
-- Key Lemmas for Assignment Transformation
-- ============================================================================

section AssignmentLemmas

/-- Map assignment commutes with domain symmetry application -/
@[simp]
lemma map_assignment_apply_symmetry {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {assignment : Assignment VarIndex DomainType} {scope : Vector VarIndex n}
    {σ : DomainSymmetryFamily VarIndex DomainType} :
    map_assignment (σ.apply assignment) scope =
    apply_symmetry_to_scope_values σ scope (map_assignment assignment scope) := by
  apply scope_values_ext
  intro i
  simp only [map_assignment, apply_symmetry_to_scope_values, DomainSymmetryFamily.apply]

end AssignmentLemmas

-- ============================================================================
-- Symmetry Preservation Theorems
-- ============================================================================

/-- Domain symmetry preserves constraint satisfaction -/
theorem constraint_symmetric_preserves_satisfaction {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {c : Constraint VarIndex DomainType n} {σ : DomainSymmetryFamily VarIndex DomainType}
    (h_symm : constraint_domain_symmetric c σ)
    (assignment : Assignment VarIndex DomainType) :
    satisfies_constraint c (σ.apply assignment) ↔ satisfies_constraint c assignment := by
  simp only [satisfies_constraint, sat_iff]
  rw [map_assignment_apply_symmetry]
  rw [h_symm]

/-- Domain symmetry preserves dynamic constraint satisfaction -/
theorem dynamic_constraint_symmetric_preserves_satisfaction {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    {dc : DynamicConstraint VarIndex DomainType} {σ : DomainSymmetryFamily VarIndex DomainType}
    (h_symm : dynamic_constraint_domain_symmetric dc σ)
    (assignment : Assignment VarIndex DomainType) :
    satisfies_dynamic_constraint dc (σ.apply assignment) ↔ satisfies_dynamic_constraint dc assignment := by
  cases dc with
  | mk n c =>
    simp only [satisfies_dynamic_constraint, dynamic_constraint_domain_symmetric] at h_symm ⊢
    exact constraint_symmetric_preserves_satisfaction h_symm assignment

/-- Domain symmetries preserve solutions -/
theorem domain_symmetry_preserves_solutions {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (σ : DomainSymmetryFamily VarIndex DomainType)
    (h_domain_sym : domain_symmetry csp σ)
    (h_constraints : ∀ c ∈ csp.constraints, dynamic_constraint_domain_symmetric c σ) :
    ∀ assignment : Assignment VarIndex DomainType,
      is_solution csp assignment → is_solution csp (σ.apply assignment) := by
  intro assignment ⟨h_valid, h_sat⟩
  constructor
  · -- Valid assignment: domain symmetry preserves domain membership
    intro v
    exact h_domain_sym v (assignment v) (h_valid v)
  · -- Satisfies constraints: use constraint symmetry
    intro c hc
    rw [dynamic_constraint_symmetric_preserves_satisfaction (h_constraints c hc)]
    exact h_sat c hc


-- ============================================================================
-- Symmetry Breaking Constraints
-- ============================================================================

/-- A constraint is a domain symmetry breaking constraint if for every solution
    of the original CSP, there exists a domain symmetry that transforms it into
    a solution of the extended CSP -/
def domain_symmetry_breaking_constraint {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) : Prop :=
  ∀ assignment : Assignment VarIndex DomainType, is_solution csp assignment →
    ∃ σ : DomainSymmetryFamily VarIndex DomainType,
      domain_symmetry csp σ ∧
      (∀ constraint ∈ csp.constraints, dynamic_constraint_domain_symmetric constraint σ) ∧
      is_solution (extended_csp csp c) (σ.apply assignment)


-- ============================================================================
-- Symmetry Breaking Preserves Satisfiability
-- ============================================================================

/-- Domain symmetry breaking constraints preserve equisatisfiability -/
theorem domain_symmetry_breaking_preserves_equisatisfiability
    {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType)
    (h_sbc : domain_symmetry_breaking_constraint csp c) :
    equisatisfiable csp (extended_csp csp c) := by
  constructor
  · -- If original CSP is satisfiable, extended CSP is satisfiable
    intro ⟨assignment, h_sol⟩
    obtain ⟨σ, h_domain_sym, h_constraint_sym, h_ext_sol⟩ := h_sbc assignment h_sol
    exact ⟨σ.apply assignment, h_ext_sol⟩
  · -- If extended CSP is satisfiable, original CSP is satisfiable
    intro ⟨assignment, h_ext_sol⟩
    -- Any solution to extended CSP is also a solution to original CSP
    have h_sol : is_solution csp assignment := by
      constructor
      · exact h_ext_sol.1
      · intro constraint h_constraint
        exact h_ext_sol.2 constraint (List.mem_cons_of_mem c h_constraint)
    exact ⟨assignment, h_sol⟩


-- ============================================================================
-- Utility Lemmas for Specific Domain Types
-- ============================================================================

section SpecificDomainSymmetries

/-- Create a domain symmetry family where all variables have the same domain type
    and use the same symmetry - this bridges to the homogeneous case -/
def uniform_domain_symmetry {VarIndex : Type} {Domain : Type}
    (σ : Equiv Domain Domain) :
    DomainSymmetryFamily VarIndex (fun _ => Domain) where
  to_equiv := fun _ => σ

/-- Create a domain symmetry family from a function that provides symmetries
    for each variable -/
def custom_domain_symmetry {VarIndex : Type} {DomainType : VarIndex → Type}
    (σ_map : (v : VarIndex) → Equiv (DomainType v) (DomainType v)) :
    DomainSymmetryFamily VarIndex DomainType where
  to_equiv := σ_map

end SpecificDomainSymmetries

-- ============================================================================
-- Composition and Group Structure
-- ============================================================================

section GroupStructure

/-- Domain symmetry families form a group under composition -/
instance {VarIndex : Type} {DomainType : VarIndex → Type} :
    Group (DomainSymmetryFamily VarIndex DomainType) where
  one := DomainSymmetryFamily.identity
  mul := DomainSymmetryFamily.comp
  inv := DomainSymmetryFamily.inv
  one_mul := by
    intro σ
    ext v x
    show (Equiv.refl _).trans (σ.to_equiv v) x = σ.to_equiv v x
    rfl
  mul_one := by
    intro σ
    ext v x
    show (σ.to_equiv v).trans (Equiv.refl _) x = σ.to_equiv v x
    rfl
  mul_assoc := by
    intro σ₁ σ₂ σ₃
    ext v x
    rfl
  inv_mul_cancel := by
    intro σ
    ext v x
    show ((σ.to_equiv v).symm).trans (σ.to_equiv v) x = (Equiv.refl _) x
    simp only [Equiv.trans_apply, Equiv.refl_apply]
    exact Equiv.apply_symm_apply (σ.to_equiv v) x

end GroupStructure

-- ============================================================================
-- Combined Symmetry Breaking Constraints
-- ============================================================================

/-- A constraint can break either domain or variable symmetries -/
def general_symmetry_breaking_constraint {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType) : Prop :=
  domain_symmetry_breaking_constraint csp c ∨ variable_symmetry_breaking_constraint csp c

/-- General symmetry breaking constraints preserve equisatisfiability -/
theorem general_symmetry_breaking_preserves_equisatisfiability
    {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) (c : DynamicConstraint VarIndex DomainType)
    (h_sbc : general_symmetry_breaking_constraint csp c) :
    equisatisfiable csp (extended_csp csp c) := by
  cases h_sbc with
  | inl h_domain => exact domain_symmetry_breaking_preserves_equisatisfiability csp c h_domain
  | inr h_variable => exact variable_symmetry_breaking_preserves_equisatisfiability csp c h_variable

end CSP
