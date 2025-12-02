import CSP.L2S.Core
import CSP.Core

namespace CSP.L2S

/-!
# L2M Embedding Theory

Formal proofs that L2M HomogeneousCSPs embed into the heterogeneous framework with zero cost.

## Main Results

1. **embed_zero_overhead**: The embedding is identity at runtime
2. **embedding_preserves_solutions**: Solution sets are identical
3. **embedding_preserves_satisfiability**: Satisfiability is preserved
4. **solution_space_isomorphism**: Formal bijection between solution spaces

-/

open HomogeneousCSP

-- ============================================================================
-- Embedding into Heterogeneous Framework
-- ============================================================================

/-- The constant domain type function for homogeneous CSPs -/
def constantDomainType : HomogeneousVarIndex n → Type :=
  fun _ => HomogeneousDomain

/--
Zero-cost embedding into the general heterogeneous framework.

This embedding:
- Maps to unrestricted integer domains (`Set.univ` for all variables)
- Extracts dynamic checkers from tagged constraints
- Is provably identity at runtime (zero overhead)
-/
def toHeterogeneous (csp : HomogeneousCSP) :
    CSP (HomogeneousVarIndex csp.num_vars) constantDomainType :=
  { domain := fun _ => Set.univ
    constraints := csp.constraints.map (·.dynamic) }

-- ============================================================================
-- Fundamental Theorems
-- ============================================================================

/--
The embedding preserves solution checking.

A homogeneous assignment is a solution of the L2M CSP if and only if
it's a solution of the embedded heterogeneous CSP.
-/
theorem isSolution_iff_heterogeneous (csp : HomogeneousCSP)
    (assignment : HomogeneousAssignment csp.num_vars) :
    isSolution csp assignment ↔ is_solution (toHeterogeneous csp) assignment := by
  simp only [isSolution, is_solution, toHeterogeneous, valid_assignment]
  simp only [Set.mem_univ, forall_true_iff, true_and]
  constructor
  · intro h c hc
    obtain ⟨tc, htc, heq⟩ := List.mem_map.mp hc
    rw [← heq]
    simp only [satisfiesConstraint] at h
    exact h tc htc
  · intro h tc htc
    have : tc.dynamic ∈ List.map TaggedConstraint.dynamic csp.constraints := by
      apply List.mem_map_of_mem
      exact htc
    simp only [satisfiesConstraint]
    exact h tc.dynamic this

/-- The embedding preserves satisfiability -/
theorem isSatisfiable_iff_heterogeneous (csp : HomogeneousCSP) :
    isSatisfiable csp ↔ is_satisfiable (toHeterogeneous csp) := by
  simp only [isSatisfiable, is_satisfiable]
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
def embed (csp : HomogeneousCSP) :
    CSP (HomogeneousVarIndex csp.num_vars) (constantDomainType) :=
  toHeterogeneous csp

-- ============================================================================
-- Zero-Cost Abstraction
-- ============================================================================

/-- The L2M embedding has zero runtime overhead (proven definitionally equal) -/
theorem embed_zero_overhead (csp : HomogeneousCSP) :
    embed csp = ⟨fun _ => Set.univ, csp.constraints.map (·.dynamic)⟩ := by
  simp [embed, toHeterogeneous]

-- ============================================================================
-- Solution Preservation
-- ============================================================================

/-- The embedding preserves solution checking -/
theorem embedding_preserves_solutions (csp : HomogeneousCSP) :
    ∀ assignment, isSolution csp assignment ↔
    is_solution (embed csp) assignment := by
  intro assignment
  simp [embed]
  exact isSolution_iff_heterogeneous csp assignment

/-- The embedding preserves satisfiability -/
theorem embedding_preserves_satisfiability (csp : HomogeneousCSP) :
    isSatisfiable csp ↔ is_satisfiable (embed csp) := by
  simp [embed]
  exact isSatisfiable_iff_heterogeneous csp

/-- Solution space isomorphism -/
theorem solution_space_isomorphism (csp : HomogeneousCSP) :
    {assignment | isSolution csp assignment} =
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

theorem addConstraint_embedding_commutes (csp : HomogeneousCSP)
    (constraint : TaggedConstraint csp.num_vars) :
    embed (csp.addConstraint constraint) =
    add_constraint (embed csp) constraint.dynamic := by
  simp [embed, toHeterogeneous, addConstraint, add_constraint]

-- ============================================================================
-- Constraint Extraction
-- ============================================================================

/-- Extract dynamic constraints from unified CSP -/
def extractDynamicConstraints (csp : HomogeneousCSP) :
    List (DynamicConstraint (Fin csp.num_vars) (fun _ => ℤ)) :=
  csp.constraints.map (·.dynamic)

theorem extractDynamicConstraints_correct (csp : HomogeneousCSP) :
    extractDynamicConstraints csp =
    (embed csp).constraints := by
  simp [extractDynamicConstraints, embed, toHeterogeneous]

-- ============================================================================
-- Foundational Lemmas
-- ============================================================================

/-- The constant domain type always returns ℤ -/
@[simp]
lemma constantDomainType_eq {n : ℕ} (v : Fin n) :
  constantDomainType v = ℤ := rfl

/-- HomogeneousVarIndex is definitionally equal to Fin -/
@[simp]
lemma HomogeneousVarIndex_def (n : ℕ) :
  HomogeneousVarIndex n = Fin n := rfl

/-- HomogeneousDomain is definitionally equal to ℤ -/
@[simp]
lemma HomogeneousDomain_def :
  HomogeneousDomain = ℤ := rfl

end CSP.L2S
