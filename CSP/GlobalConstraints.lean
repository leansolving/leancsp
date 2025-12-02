import CSP.Core
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.FinRange
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Basic

namespace CSP

open Function List

-- ============================================================================
-- Helper Functions for Type-Safe Constraint Construction
-- ============================================================================

section Helpers

/-- Extract values from ScopeValues when all variables have the same type -/
def extractHomogeneousValues {VarIndex : Type} {DomainType : VarIndex → Type} {D : Type}
    {scope : _root_.Vector VarIndex n} (h : ∀ i : Fin n, DomainType (scope.get i) = D)
    (values : ScopeValues VarIndex DomainType scope) : List D :=
  List.ofFn fun i => cast (h i) (values i)

end Helpers

-- ============================================================================
-- All Different Constraints (Type-Specific Versions)
-- ============================================================================

section AllDifferent

/-- All different constraint for natural numbers -/
def alldifferent_nat {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = ℕ) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide vals.Nodup

/-- All different constraint for integers -/
def alldifferent_int {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Int) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide vals.Nodup

/-- All different constraint for strings -/
def alldifferent_string {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = String) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide vals.Nodup

/-- All different constraint for finite types -/
def alldifferent_fin {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (k : ℕ) (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Fin k) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide vals.Nodup

/-- All different constraint for booleans -/
def alldifferent_bool {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Bool) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide vals.Nodup

-- Dynamic constraint constructors
def alldifferent_nat_dynamic {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = ℕ) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk n (alldifferent_nat scope h)

def alldifferent_int_dynamic {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Int) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk n (alldifferent_int scope h)

def alldifferent_fin_dynamic {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (k : ℕ) (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Fin k) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk n (alldifferent_fin k scope h)

end AllDifferent

-- ============================================================================
-- Sum Equals Constraints (Type-Specific Versions)
-- ============================================================================

section SumEquals

/-- Sum equals constraint for natural numbers -/
def sum_eq_nat {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = ℕ)
    (target : ℕ) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide (vals.sum = target)

/-- Sum equals constraint for integers -/
def sum_eq_int {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Int)
    (target : Int) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide (vals.sum = target)

/-- Sum equals constraint for finite types (using their numeric value) -/
def sum_eq_fin {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (k : ℕ) (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Fin k)
    (target : ℕ) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide ((vals.map Fin.val).sum = target)

-- Dynamic constraint constructors
def sum_eq_nat_dynamic {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = ℕ)
    (target : ℕ) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk n (sum_eq_nat scope h target)

def sum_eq_int_dynamic {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Int)
    (target : Int) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk n (sum_eq_int scope h target)

end SumEquals

-- ============================================================================
-- Count Constraints (Type-Specific Versions)
-- ============================================================================

section Count

/-- Count constraint for natural numbers -/
def count_nat {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = ℕ)
    (value : ℕ) (target : ℕ) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide (vals.count value = target)

/-- Count constraint for booleans -/
def count_bool {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Bool)
    (value : Bool) (target : ℕ) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide (vals.count value = target)

/-- Count constraint for finite types -/
def count_fin {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (k : ℕ) (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Fin k)
    (value : Fin k) (target : ℕ) : Constraint VarIndex DomainType n where
  scope := scope
  check := fun values => 
    let vals := extractHomogeneousValues h values
    decide (vals.count value = target)

-- Specialized count true for booleans
def count_true {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (scope : _root_.Vector VarIndex n)
    (h : ∀ i : Fin n, DomainType (scope.get i) = Bool)
    (target : ℕ) : Constraint VarIndex DomainType n :=
  count_bool scope h true target

end Count

-- ============================================================================
-- Domain-Specific Constraints
-- ============================================================================

section DomainSpecific

/-- Diagonal constraint for N-Queens and similar problems -/
def diagonal_safe {n : ℕ} [NeZero n] : Constraint (Fin n) (fun _ => Fin n) n where
  scope := _root_.Vector.ofFn id
  check := fun values => 
    decide (∀ i j : Fin n, i < j → 
      let vi := values i
      let vj := values j
      (vi.val + i.val ≠ vj.val + j.val) ∧  -- Positive diagonal
      (vi.val + j.val ≠ vj.val + i.val))   -- Negative diagonal

/-- N-Queens combined constraint (all different + diagonal safe) -/
def nqueens {n : ℕ} [NeZero n] : Constraint (Fin n) (fun _ => Fin n) n where
  scope := _root_.Vector.ofFn id
  check := fun values => 
    -- All queens in different columns
    decide ((List.ofFn values).Nodup) &&
    -- No two queens on same diagonal
    decide (∀ i j : Fin n, i < j → 
      let vi := values i
      let vj := values j
      (vi.val + i.val ≠ vj.val + j.val) ∧  -- Positive diagonal
      (vi.val + j.val ≠ vj.val + i.val))   -- Negative diagonal

end DomainSpecific

-- ============================================================================
-- Utility Functions
-- ============================================================================

section Utilities

/-- Convert constraint to dynamic constraint -/
def to_dynamic {VarIndex : Type} {DomainType : VarIndex → Type} 
    (c : Constraint VarIndex DomainType n) : DynamicConstraint VarIndex DomainType :=
  DynamicConstraint.mk n c

/-- Create a vector from two elements -/
def vector_pair {α : Type} (a b : α) : _root_.Vector α 2 := ⟨#[a, b], rfl⟩

/-- Create a vector from three elements -/
def vector_triple {α : Type} (a b c : α) : _root_.Vector α 3 := ⟨#[a, b, c], rfl⟩

end Utilities

end CSP