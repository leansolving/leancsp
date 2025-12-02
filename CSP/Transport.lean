-- Transport utilities for dependent type theory in CSP
-- This file contains general transport lemmas for working with type equalities
-- and dependent types in constraint satisfaction problems.

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Equiv.Basic

namespace CSP

-- ============================================================================
-- Core Transport Lemmas  
-- ============================================================================

section CoreTransport

universe u

/-- The fundamental transport principle for set membership:
    cast and Eq.mpr are compatible for set membership.
    This is the key lemma needed for variable symmetry preservation
    in heterogeneous domain CSPs. -/
@[simp] 
theorem mem_cast_iff {α β : Type u} (h : α = β) (s : Set α) (x : α) :
    (cast h x : β) ∈ (h ▸ s : Set β) ↔ x ∈ s := by
  cases h        -- turns h into rfl and rewrites all occurrences
  simp           -- everything becomes definitionally equal

/-- Alternative formulation using h.symm for the set transport -/
@[simp]
theorem mem_cast_iff_symm {α β : Type u} (h : α = β) (s : Set α) (x : α) :
    (cast h x : β) ∈ (h.symm ▸ s : Set β) ↔ x ∈ s := by
  cases h
  simp

/-- Version using Eq.mpr with h.symm for the set transport -/
@[simp]
theorem mem_cast_iff_mpr_symm {α β : Type u} (h : α = β) (s : Set α) (x : α) :
    (cast h x : β) ∈ (Eq.mpr (congrArg Set h.symm) s : Set β) ↔ x ∈ s := by
  cases h
  simp

end CoreTransport

end CSP