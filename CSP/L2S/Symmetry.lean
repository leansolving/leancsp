import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.Symmetry
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Ring

namespace CSP.L2S

/-!
# L2M Symmetry Theory

Symmetry-breaking theory for L2M HomogeneousCSPs with integer domains.

## Symmetry Types

1. **Domain Symmetry**: Permutation of ℤ preserving all constraints
2. **Variable Symmetry**: Permutation of variables preserving all constraints
3. **Symmetry Breaking**: Constraint that when added, preserves equisatisfiability

## Main Results

- `domain_symmetry_preserves_solutions`: Domain symmetries preserve solution sets
- `variable_symmetry_preserves_solutions`: Variable symmetries preserve solution sets
- `symmetry_breaking_preserves_equisatisfiability`: Adding symmetry-breaking constraints preserves satisfiability
-/

open HomogeneousCSP

-- ============================================================================
-- Core Symmetry Definitions
-- ============================================================================

/-- Domain symmetry: a permutation of ℤ that preserves all constraints -/
def DomainSymmetry (csp : HomogeneousCSP) (δ : Equiv.Perm HomogeneousDomain) : Prop :=
  ∀ assignment : HomogeneousAssignment csp.num_vars,
  isSolution csp assignment →
  isSolution csp (δ ∘ assignment)

/-- Variable symmetry: a permutation of variable indices that preserves all constraints -/
def VariableSymmetry (csp : HomogeneousCSP)
    (β : Equiv.Perm (HomogeneousVarIndex csp.num_vars)) : Prop :=
  ∀ assignment : HomogeneousAssignment csp.num_vars,
  isSolution csp assignment →
  isSolution csp (assignment ∘ β)

-- ============================================================================
-- Common Domain Symmetries
-- ============================================================================

namespace DomainSymmetry

/-- Identity domain symmetry -/
def identity : Equiv.Perm HomogeneousDomain := Equiv.refl _

/-- Swap two values in the integer domain -/
def swap (i j : HomogeneousDomain) : Equiv.Perm HomogeneousDomain :=
  Equiv.swap i j

/-- Negation symmetry: flip the sign of all values -/
def negation : Equiv.Perm HomogeneousDomain where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := fun x => by simp
  right_inv := fun x => by simp

/-- Translation symmetry: add a constant offset -/
def translate (offset : ℤ) : Equiv.Perm HomogeneousDomain where
  toFun := fun x => x + offset
  invFun := fun x => x - offset
  left_inv := fun x => by ring
  right_inv := fun x => by ring

/-- Identity is always a domain symmetry -/
theorem identity_is_symmetry (csp : HomogeneousCSP) :
    DomainSymmetry csp identity := by
  intro assignment h_solution
  simp only [identity]
  exact h_solution

end DomainSymmetry

-- ============================================================================
-- Common Variable Symmetries
-- ============================================================================

namespace VariableSymmetry

/-- Identity variable symmetry -/
def identity (num_vars : ℕ) : Equiv.Perm (HomogeneousVarIndex num_vars) := Equiv.refl _

/-- Swap two variables -/
def swap {num_vars : ℕ} (i j : HomogeneousVarIndex num_vars) :
    Equiv.Perm (HomogeneousVarIndex num_vars) :=
  Equiv.swap i j

/-- Identity is always a variable symmetry -/
theorem identity_is_symmetry (csp : HomogeneousCSP) :
    VariableSymmetry csp (identity csp.num_vars) := by
  intro assignment h_solution
  simp only [identity]
  exact h_solution

end VariableSymmetry

-- ============================================================================
-- Constraint Symmetry Properties
-- ============================================================================

/-- A dynamic constraint is domain symmetric if it's invariant under domain permutations -/
def constraintDomainSymmetric {num_vars : ℕ}
    (c : DynamicConstraint (HomogeneousVarIndex num_vars) (fun _ => HomogeneousDomain))
    (δ : Equiv.Perm HomogeneousDomain) : Prop :=
  ∀ assignment : HomogeneousAssignment num_vars,
    satisfies_dynamic_constraint c assignment →
    satisfies_dynamic_constraint c (δ ∘ assignment)

/-- A dynamic constraint is variable symmetric if it's invariant under variable permutations -/
def constraintVariableSymmetric {num_vars : ℕ}
    (c : DynamicConstraint (HomogeneousVarIndex num_vars) (fun _ => HomogeneousDomain))
    (β : Equiv.Perm (HomogeneousVarIndex num_vars)) : Prop :=
  ∀ assignment : HomogeneousAssignment num_vars,
    satisfies_dynamic_constraint c assignment →
    satisfies_dynamic_constraint c (assignment ∘ β)

/-- A tagged constraint is domain symmetric if its dynamic part is -/
def taggedConstraintDomainSymmetric {num_vars : ℕ}
    (tc : TaggedConstraint num_vars)
    (δ : Equiv.Perm HomogeneousDomain) : Prop :=
  constraintDomainSymmetric tc.dynamic δ

/-- A tagged constraint is variable symmetric if its dynamic part is -/
def taggedConstraintVariableSymmetric {num_vars : ℕ}
    (tc : TaggedConstraint num_vars)
    (β : Equiv.Perm (HomogeneousVarIndex num_vars)) : Prop :=
  constraintVariableSymmetric tc.dynamic β

-- ============================================================================
-- Symmetry Preservation Theorems
-- ============================================================================

/-- Domain symmetries preserve solutions when all constraints are symmetric -/
theorem domain_symmetry_preserves_solutions (csp : HomogeneousCSP)
    (δ : Equiv.Perm HomogeneousDomain)
    (h_constraints : ∀ c ∈ csp.constraints, taggedConstraintDomainSymmetric c δ) :
    DomainSymmetry csp δ := by
  intro assignment h_solution tc h_tc_mem
  have h_symmetric := h_constraints tc h_tc_mem
  unfold taggedConstraintDomainSymmetric constraintDomainSymmetric at h_symmetric
  exact h_symmetric assignment (h_solution tc h_tc_mem)

/-- Variable symmetries preserve solutions when all constraints are symmetric -/
theorem variable_symmetry_preserves_solutions (csp : HomogeneousCSP)
    (β : Equiv.Perm (HomogeneousVarIndex csp.num_vars))
    (h_constraints : ∀ c ∈ csp.constraints, taggedConstraintVariableSymmetric c β) :
    VariableSymmetry csp β := by
  intro assignment h_solution tc h_tc_mem
  have h_symmetric := h_constraints tc h_tc_mem
  unfold taggedConstraintVariableSymmetric constraintVariableSymmetric at h_symmetric
  exact h_symmetric assignment (h_solution tc h_tc_mem)

-- ============================================================================
-- Symmetry Breaking Constraints
-- ============================================================================

/-- A domain symmetry breaking constraint: for every solution, there exists a domain
    symmetry transforming it to a solution of the extended CSP -/
def domainSymmetryBreakingConstraint (csp : HomogeneousCSP)
    (c : TaggedConstraint csp.num_vars) : Prop :=
  ∀ assignment : HomogeneousAssignment csp.num_vars,
  isSolution csp assignment →
  ∃ δ : Equiv.Perm HomogeneousDomain,
    DomainSymmetry csp δ ∧
    isSolution (csp.addConstraint c) (δ ∘ assignment)

/-- A variable symmetry breaking constraint: for every solution, there exists a variable
    symmetry transforming it to a solution of the extended CSP -/
def variableSymmetryBreakingConstraint (csp : HomogeneousCSP)
    (c : TaggedConstraint csp.num_vars) : Prop :=
  ∀ assignment : HomogeneousAssignment csp.num_vars,
  isSolution csp assignment →
  ∃ β : Equiv.Perm (HomogeneousVarIndex csp.num_vars),
    VariableSymmetry csp β ∧
    isSolution (csp.addConstraint c) (assignment ∘ β)

/-- General symmetry breaking constraint: breaks either domain or variable symmetries -/
def symmetryBreakingConstraint (csp : HomogeneousCSP)
    (c : TaggedConstraint csp.num_vars) : Prop :=
  domainSymmetryBreakingConstraint csp c ∨
  variableSymmetryBreakingConstraint csp c

-- ============================================================================
-- Soundness Theorems
-- ============================================================================

/-- Domain symmetry breaking constraints preserve satisfiability -/
theorem domainSymmetryBreaking_preserves_satisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_satisfiable : isSatisfiable csp)
    (h_sbc : domainSymmetryBreakingConstraint csp c) :
    isSatisfiable (csp.addConstraint c) := by
  obtain ⟨assignment, h_solution⟩ := h_satisfiable
  obtain ⟨δ, h_symmetry, h_solution'⟩ := h_sbc assignment h_solution
  exact ⟨δ ∘ assignment, h_solution'⟩

/-- Variable symmetry breaking constraints preserve satisfiability -/
theorem variableSymmetryBreaking_preserves_satisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_satisfiable : isSatisfiable csp)
    (h_sbc : variableSymmetryBreakingConstraint csp c) :
    isSatisfiable (csp.addConstraint c) := by
  obtain ⟨assignment, h_solution⟩ := h_satisfiable
  obtain ⟨β, h_symmetry, h_solution'⟩ := h_sbc assignment h_solution
  exact ⟨assignment ∘ β, h_solution'⟩

/-- General symmetry breaking preserves satisfiability -/
theorem symmetryBreaking_preserves_satisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_satisfiable : isSatisfiable csp)
    (h_sbc : symmetryBreakingConstraint csp c) :
    isSatisfiable (csp.addConstraint c) := by
  unfold symmetryBreakingConstraint at h_sbc
  obtain h_domain | h_variable := h_sbc
  · exact domainSymmetryBreaking_preserves_satisfiability csp c h_satisfiable h_domain
  · exact variableSymmetryBreaking_preserves_satisfiability csp c h_satisfiable h_variable

-- ============================================================================
-- Equisatisfiability Results
-- ============================================================================

/-- Domain symmetry breaking implies equisatisfiability -/
theorem domainSymmetryBreaking_equisatisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_sbc : domainSymmetryBreakingConstraint csp c) :
    equisatisfiable csp (csp.addConstraint c) := by
  constructor
  · intro h_satisfiable
    exact domainSymmetryBreaking_preserves_satisfiability csp c h_satisfiable h_sbc
  · intro h_satisfiable'
    obtain ⟨assignment, h_solution'⟩ := h_satisfiable'
    use assignment
    -- Show assignment is a solution to csp
    intro constraint h_constraint_in_csp
    -- Since addConstraint contains all constraints of csp
    have h_constraint_in_extended : constraint ∈ (csp.addConstraint c).constraints := by
      simp only [addConstraint]
      exact List.mem_cons_of_mem c h_constraint_in_csp
    exact h_solution' constraint h_constraint_in_extended

/-- Variable symmetry breaking implies equisatisfiability -/
theorem variableSymmetryBreaking_equisatisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_sbc : variableSymmetryBreakingConstraint csp c) :
    equisatisfiable csp (csp.addConstraint c) := by
  constructor
  · intro h_satisfiable
    exact variableSymmetryBreaking_preserves_satisfiability csp c h_satisfiable h_sbc
  · intro h_satisfiable'
    obtain ⟨assignment, h_solution'⟩ := h_satisfiable'
    use assignment
    -- Show assignment is a solution to csp
    intro constraint h_constraint_in_csp
    -- Since addConstraint contains all constraints of csp
    have h_constraint_in_extended : constraint ∈ (csp.addConstraint c).constraints := by
      simp only [addConstraint]
      exact List.mem_cons_of_mem c h_constraint_in_csp
    exact h_solution' constraint h_constraint_in_extended

/-- General symmetry breaking implies equisatisfiability -/
theorem symmetryBreaking_equisatisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_sbc : symmetryBreakingConstraint csp c) :
    equisatisfiable csp (csp.addConstraint c) := by
  unfold symmetryBreakingConstraint at h_sbc
  obtain h_domain | h_variable := h_sbc
  · exact domainSymmetryBreaking_equisatisfiability csp c h_domain
  · exact variableSymmetryBreaking_equisatisfiability csp c h_variable

-- ============================================================================
-- Compatibility with Heterogeneous Framework
-- ============================================================================

/-- Domain symmetry breaking preserves heterogeneous equisatisfiability via embedding -/
theorem domainSymmetryBreaking_heterogeneous_equisatisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_sbc : domainSymmetryBreakingConstraint csp c) :
    CSP.equisatisfiable (embed csp) (embed (csp.addConstraint c)) := by
  have h_native := domainSymmetryBreaking_equisatisfiability csp c h_sbc
  rw [CSP.equisatisfiable]
  constructor
  · intro h_sat
    have h_sat_L2M := (embedding_preserves_satisfiability csp).mpr h_sat
    have h_sat' := h_native.1 h_sat_L2M
    exact (embedding_preserves_satisfiability (csp.addConstraint c)).mp h_sat'
  · intro h_sat'
    have h_sat'_L2M := (embedding_preserves_satisfiability (csp.addConstraint c)).mpr h_sat'
    have h_sat := h_native.2 h_sat'_L2M
    exact (embedding_preserves_satisfiability csp).mp h_sat

/-- Variable symmetry breaking preserves heterogeneous equisatisfiability via embedding -/
theorem variableSymmetryBreaking_heterogeneous_equisatisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_sbc : variableSymmetryBreakingConstraint csp c) :
    CSP.equisatisfiable (embed csp) (embed (csp.addConstraint c)) := by
  have h_native := variableSymmetryBreaking_equisatisfiability csp c h_sbc
  rw [CSP.equisatisfiable]
  constructor
  · intro h_sat
    have h_sat_L2M := (embedding_preserves_satisfiability csp).mpr h_sat
    have h_sat' := h_native.1 h_sat_L2M
    exact (embedding_preserves_satisfiability (csp.addConstraint c)).mp h_sat'
  · intro h_sat'
    have h_sat'_L2M := (embedding_preserves_satisfiability (csp.addConstraint c)).mpr h_sat'
    have h_sat := h_native.2 h_sat'_L2M
    exact (embedding_preserves_satisfiability csp).mp h_sat

/-- General symmetry breaking preserves heterogeneous equisatisfiability via embedding -/
theorem symmetryBreaking_heterogeneous_equisatisfiability
    (csp : HomogeneousCSP) (c : TaggedConstraint csp.num_vars)
    (h_sbc : symmetryBreakingConstraint csp c) :
    CSP.equisatisfiable (embed csp) (embed (csp.addConstraint c)) := by
  unfold symmetryBreakingConstraint at h_sbc
  obtain h_domain | h_variable := h_sbc
  · exact domainSymmetryBreaking_heterogeneous_equisatisfiability csp c h_domain
  · exact variableSymmetryBreaking_heterogeneous_equisatisfiability csp c h_variable

-- ============================================================================
-- Bound Constraint Preservation
-- ============================================================================

/-!
### Bound Constraint Preservation Under Symmetries

This section proves that bound constraints are preserved under domain and variable symmetries.

**Key Theorems:**
1. **intervalPreserving_preserves_bound**: Interval-preserving domain perms preserve bounds
2. **domainSymmetry_preserves_bounds**: Domain symmetry preserves bound constraint lists
3. **variableSymmetry_preserves_bounds**: Variable symmetry preserves bounds (always)

-/

/-- Check if a permutation preserves an interval [lb, ub] ⊆ ℤ -/
def intervalPreserving (δ : Equiv.Perm ℤ) (lb ub : ℤ) : Prop :=
  ∀ d : ℤ, (lb ≤ d ∧ d ≤ ub) ↔ (lb ≤ δ d ∧ δ d ≤ ub)

/-- Helper: Extract the bound constraint from a tagged constraint if it is one -/
def isBoundConstraint {num_vars : ℕ} (tc : TaggedConstraint num_vars) : Option (ℕ × ℤ × ℤ) :=
  match tc.pattern with
  | ConstraintPattern.bound var lb ub => some (var, lb, ub)
  | _ => none

/-- Interval-preserving domain permutations preserve individual bound constraints -/
theorem intervalPreserving_preserves_bound {num_vars : ℕ}
    (δ : Equiv.Perm HomogeneousDomain) (v : HomogeneousVarIndex num_vars) (lb ub : ℤ)
    (h_interval : intervalPreserving δ lb ub)
    (assignment : HomogeneousAssignment num_vars) :
    satisfies_dynamic_constraint (bound v lb ub).dynamic assignment ↔
    satisfies_dynamic_constraint (bound v lb ub).dynamic (δ ∘ assignment) := by
  -- Unfold constraint satisfaction definitions
  simp only [bound, satisfies_dynamic_constraint, satisfies_constraint, sat]
  -- The constraint has scope #v[v], so map_assignment extracts assignment at v
  have h1 : extractValues (map_assignment assignment (⟨#[v], rfl⟩ : _root_.Vector _ 1)) = [assignment v] := by
    simp [extractValues, map_assignment, List.ofFn, _root_.Vector.get]
    rfl
  have h2 : extractValues (map_assignment (δ ∘ assignment) (⟨#[v], rfl⟩ : _root_.Vector _ 1)) = [δ (assignment v)] := by
    simp [extractValues, map_assignment, List.ofFn, _root_.Vector.get, Function.comp_apply]
    rfl
  -- Rewrite using these simplifications
  rw [h1, h2]
  -- Now both sides match on [val] giving: decide (lb ≤ val ∧ val ≤ ub) = true
  simp only [decide_eq_true_iff]
  -- Apply interval preservation
  exact h_interval (assignment v)

/-- Domain permutation preserves a list of bound constraints when interval-preserving -/
theorem domainSymmetry_preserves_bound_list {num_vars : ℕ}
    (δ : Equiv.Perm HomogeneousDomain)
    (bounds : List (HomogeneousVarIndex num_vars × ℤ × ℤ))
    (h_interval : ∀ (v lb ub), (v, lb, ub) ∈ bounds → intervalPreserving δ lb ub)
    (assignment : HomogeneousAssignment num_vars) :
    (∀ (v lb ub), (v, lb, ub) ∈ bounds →
      satisfies_dynamic_constraint (bound v lb ub).dynamic assignment) ↔
    (∀ (v lb ub), (v, lb, ub) ∈ bounds →
      satisfies_dynamic_constraint (bound v lb ub).dynamic (δ ∘ assignment)) := by
  constructor
  · intro h v lb ub h_mem
    have h_sat := h v lb ub h_mem
    have h_preserves := intervalPreserving_preserves_bound δ v lb ub (h_interval v lb ub h_mem) assignment
    exact h_preserves.mp h_sat
  · intro h v lb ub h_mem
    have h_sat := h v lb ub h_mem
    have h_preserves := intervalPreserving_preserves_bound δ v lb ub (h_interval v lb ub h_mem) assignment
    exact h_preserves.mpr h_sat

/-- Variable permutation preserves bound constraints (always, regardless of interval) -/
theorem variableSymmetry_preserves_bound {num_vars : ℕ}
    (β : Equiv.Perm (HomogeneousVarIndex num_vars))
    (v : HomogeneousVarIndex num_vars) (lb ub : ℤ)
    (assignment : HomogeneousAssignment num_vars) :
    satisfies_dynamic_constraint (bound v lb ub).dynamic assignment ↔
    satisfies_dynamic_constraint (bound (β v) lb ub).dynamic (assignment ∘ β.symm) := by
  -- Unfold constraint satisfaction definitions
  simp only [bound, satisfies_dynamic_constraint, satisfies_constraint, sat]
  -- Show that both sides extract the same value
  have h1 : extractValues (map_assignment assignment (⟨#[v], rfl⟩ : _root_.Vector _ 1)) = [assignment v] := by
    simp [extractValues, map_assignment, List.ofFn, _root_.Vector.get]
    rfl
  have h2 : extractValues (map_assignment (assignment ∘ β.symm) (⟨#[β v], rfl⟩ : _root_.Vector _ 1)) = [assignment v] := by
    -- The key property: (assignment ∘ β.symm) (β v) = assignment v
    have key : (assignment ∘ β.symm) (β v) = assignment v := by
      simp only [Function.comp_apply]
      rw [Equiv.symm_apply_apply]
    -- Unfold and use List.ofFn lemma for Fin 1
    unfold extractValues map_assignment
    let scope := (⟨#[β v], rfl⟩ : _root_.Vector _ 1)
    have list_eq : List.ofFn (fun i : Fin 1 => (assignment ∘ β.symm) (scope.get i)) =
                   [(assignment ∘ β.symm) (scope.get ⟨0, by norm_num⟩)] := by
      rw [List.ofFn_succ, List.ofFn_zero]
      rfl
    rw [list_eq]
    -- Show that scope.get ⟨0, _⟩ = β v
    have scope_eq : scope.get ⟨0, by norm_num⟩ = β v := by
      simp only [_root_.Vector.get, scope]
      rfl
    rw [scope_eq, key]
  -- Rewrite using these simplifications
  rw [h1, h2]

-- ============================================================================
-- Utility Functions
-- ============================================================================

/-- Composition of domain symmetries is a domain symmetry -/
theorem domainSymmetry_comp (csp : HomogeneousCSP)
    (δ₁ δ₂ : Equiv.Perm HomogeneousDomain)
    (h₁ : DomainSymmetry csp δ₁) (h₂ : DomainSymmetry csp δ₂) :
    DomainSymmetry csp (δ₁.trans δ₂) := by
  intro assignment h_solution
  have h₁_sol := h₁ assignment h_solution
  have h₂_sol := h₂ (δ₁ ∘ assignment) h₁_sol
  simp only [Equiv.trans, Equiv.coe_fn_mk] at h₂_sol ⊢
  convert h₂_sol using 1

end CSP.L2S
