import CSP.L2S.Core
import CSP.Core

namespace CSP.L2S

/-!
# L2M Embedding Theory

Formal proofs that L2M IntCSPs embed into the heterogeneous framework with zero cost.

## Main Results

1. **embed_zero_overhead**: The embedding is identity at runtime
2. **embedding_preserves_solutions**: Solution sets are identical
3. **embedding_preserves_satisfiability**: Satisfiability is preserved
4. **solution_space_isomorphism**: Formal bijection between solution spaces

-/

open IntCSP

-- ============================================================================
-- Embedding into Heterogeneous Framework
-- ============================================================================

/-- The constant domain type function for homogeneous CSPs -/
def constantDomainType : VarType n → Type :=
  fun _ => IntDomain

/--
Zero-cost embedding into the general heterogeneous framework.

This embedding:
- Maps to unrestricted integer domains (`Set.univ` for all variables)
- Extracts dynamic checkers from tagged constraints
- Is provably identity at runtime (zero overhead)
-/
def toHeterogeneous (csp : IntCSP) :
    CSP (VarType csp.num_vars) constantDomainType :=
  { domain := fun _ => Set.univ
    constraints := csp.constraints.map toDynamic }

-- ============================================================================
-- Fundamental Theorems
-- ============================================================================

/--
The embedding preserves solution checking.

A homogeneous assignment is a solution of the L2M CSP if and only if
it's a solution of the embedded heterogeneous CSP.
-/
theorem isSolution_iff_heterogeneous (csp : IntCSP)
    (assignment : IntAssignment csp.num_vars) :
    isSolutionInt csp assignment ↔ is_solution (toHeterogeneous csp) assignment := by
  simp only [isSolutionInt, is_solution, toHeterogeneous, valid_assignment]
  simp only [Set.mem_univ, forall_true_iff, true_and]
  constructor
  · intro h c hc
    obtain ⟨tc, htc, heq⟩ := List.mem_map.mp hc
    rw [← heq]
    exact (satisfiesConstraintInt_iff_toDynamic tc assignment).mp (h tc htc)
  · intro h tc htc
    refine (satisfiesConstraintInt_iff_toDynamic tc assignment).mpr (h (toDynamic tc) ?_)
    exact List.mem_map.mpr ⟨tc, htc, rfl⟩

/-- The embedding preserves satisfiability -/
theorem isSatisfiable_iff_heterogeneous (csp : IntCSP) :
    isSatisfiableInt csp ↔ is_satisfiable (toHeterogeneous csp) := by
  simp only [isSatisfiableInt, is_satisfiable]
  constructor
  · intro ⟨assignment, h_sol⟩
    use assignment
    exact (isSolution_iff_heterogeneous csp assignment).mp h_sol
  · intro ⟨assignment, h_sol⟩
    use assignment
    exact (isSolution_iff_heterogeneous csp assignment).mpr h_sol


-- ============================================================================
-- Embedding Function
-- ============================================================================

/-- The embedding function from L2M integer CSPs to heterogeneous CSPs -/
def embed (csp : IntCSP) :
    CSP (VarType csp.num_vars) (constantDomainType) :=
  toHeterogeneous csp

-- ============================================================================
-- Zero-Cost Abstraction
-- ============================================================================

/-- The L2M embedding has zero runtime overhead (proven definitionally equal) -/
theorem embed_zero_overhead (csp : IntCSP) :
    embed csp = ⟨fun _ => Set.univ, csp.constraints.map toDynamic⟩ := by
  simp [embed, toHeterogeneous]

-- ============================================================================
-- Solution Preservation
-- ============================================================================

/-- The embedding preserves solution checking -/
theorem embedding_preserves_solutions (csp : IntCSP) :
    ∀ assignment, isSolutionInt csp assignment ↔
    is_solution (embed csp) assignment := by
  intro assignment
  simp [embed]
  exact isSolution_iff_heterogeneous csp assignment

/-- The embedding preserves satisfiability -/
theorem embedding_preserves_satisfiability (csp : IntCSP) :
    isSatisfiableInt csp ↔ is_satisfiable (embed csp) := by
  simp [embed]
  exact isSatisfiable_iff_heterogeneous csp

/-- Solution space isomorphism -/
theorem solution_space_isomorphism (csp : IntCSP) :
    {assignment | isSolutionInt csp assignment} =
    {assignment | is_solution (embed csp) assignment} := by
  ext assignment
  exact embedding_preserves_solutions csp assignment

-- ============================================================================
-- Construction Operation Preservation
-- ============================================================================

theorem mkEmpty_embedding_preservation (num_vars : ℕ) :
    embed (mkEmpty num_vars) =
    CSP.mk (fun _ => Set.univ) [] := by
  simp [embed, toHeterogeneous, mkEmpty]

theorem addConstraint_embedding_commutes (csp : IntCSP)
    (constraint : IntConstraint csp.num_vars) :
    embed (csp.addConstraint constraint) =
    add_constraint (embed csp) (toDynamic constraint) := by
  simp [embed, toHeterogeneous, addConstraint, add_constraint]

-- ============================================================================
-- Constraint Extraction
-- ============================================================================

/-- Extract dynamic constraints from unified CSP -/
def extractDynamicConstraints (csp : IntCSP) :
    List (DynamicConstraint (Fin csp.num_vars) (fun _ => ℤ)) :=
  csp.constraints.map toDynamic

theorem extractDynamicConstraints_correct (csp : IntCSP) :
    extractDynamicConstraints csp =
    (embed csp).constraints := by
  rfl

-- ============================================================================
-- Foundational Lemmas
-- ============================================================================

/-- The constant domain type always returns ℤ -/
@[simp]
lemma constantDomainType_eq {n : ℕ} (v : Fin n) :
  constantDomainType v = ℤ := rfl

/-- VarType is definitionally equal to Fin -/
@[simp]
lemma VarType_def (n : ℕ) :
  VarType n = Fin n := rfl

/-- IntDomain is definitionally equal to ℤ -/
@[simp]
lemma IntDomain_def :
  IntDomain = ℤ := rfl

end CSP.L2S
