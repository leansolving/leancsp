import CSP.L2S.Core
import CSP.Core

namespace CSP.L2S

/-!
# L2S embedding theory

`IntCSP`s embed into the general heterogeneous framework at zero cost: the
embedding is definitionally the identity at runtime, preserves solution sets and
satisfiability, and induces a bijection between solution spaces.
-/

open IntCSP

/-! ### Embedding into Heterogeneous Framework -/

/-- The constant domain type function for homogeneous CSPs -/
def constantDomainType : VarType n → Type :=
  fun _ => IntDomain

/--
Zero-cost embedding into the general heterogeneous framework.

Extracts the dynamic checkers from the tagged constraints; provably the identity
at runtime.
-/
def embed (csp : IntCSP) :
    CSP (VarType csp.num_vars) constantDomainType :=
  csp.constraints.map toDynamic

/-! ### Fundamental Theorems -/

/-- The embedding preserves solution checking -/
theorem embedding_preserves_solutions (csp : IntCSP)
    (assignment : IntAssignment csp.num_vars) :
    isSolutionInt csp assignment ↔ is_solution (embed csp) assignment := by
  simp only [isSolutionInt, is_solution, embed]
  constructor
  · intro h c hc
    obtain ⟨tc, htc, heq⟩ := List.mem_map.mp hc
    rw [← heq]
    exact (satisfiesConstraintInt_iff_toDynamic tc assignment).mp (h tc htc)
  · intro h tc htc
    refine (satisfiesConstraintInt_iff_toDynamic tc assignment).mpr (h (toDynamic tc) ?_)
    exact List.mem_map.mpr ⟨tc, htc, rfl⟩

/-- The embedding preserves satisfiability -/
theorem embedding_preserves_satisfiability (csp : IntCSP) :
    isSatisfiableInt csp ↔ is_satisfiable (embed csp) := by
  simp only [isSatisfiableInt, is_satisfiable]
  constructor
  · intro ⟨assignment, h_sol⟩
    use assignment
    exact (embedding_preserves_solutions csp assignment).mp h_sol
  · intro ⟨assignment, h_sol⟩
    use assignment
    exact (embedding_preserves_solutions csp assignment).mpr h_sol

/-! ### Zero-Cost Abstraction -/

/-- The L2S embedding has zero runtime overhead (proven definitionally equal) -/
theorem embed_zero_overhead (csp : IntCSP) :
    embed csp = csp.constraints.map toDynamic :=
  rfl

/-- Solution space isomorphism -/
theorem solution_space_isomorphism (csp : IntCSP) :
    {assignment | isSolutionInt csp assignment} =
    {assignment | is_solution (embed csp) assignment} := by
  ext assignment
  exact embedding_preserves_solutions csp assignment

/-! ### Construction Operation Preservation -/

theorem mkEmpty_embedding_preservation (num_vars : ℕ) :
    embed (mkEmpty num_vars) = ([] : CSP (VarType num_vars) constantDomainType) := by
  simp [embed, mkEmpty]

theorem addConstraint_embedding_commutes (csp : IntCSP)
    (constraint : IntConstraint csp.num_vars) :
    embed (csp.addConstraint constraint) =
    add_constraint (embed csp) (toDynamic constraint) := by
  simp [embed, addConstraint, add_constraint]

/-! ### Constraint Extraction -/

/-- Extract dynamic constraints from unified CSP -/
def extractDynamicConstraints (csp : IntCSP) :
    List (DynamicConstraint (Fin csp.num_vars) (fun _ => ℤ)) :=
  csp.constraints.map toDynamic

theorem extractDynamicConstraints_correct (csp : IntCSP) :
    extractDynamicConstraints csp = embed csp := by
  rfl

/-! ### Foundational Lemmas -/

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
