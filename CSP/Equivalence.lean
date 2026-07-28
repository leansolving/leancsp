import CSP.Core
import Mathlib.Logic.Function.Basic

namespace CSP

/-! ### Solution Sets and Equivalence Relations for Heterogeneous Domain CSPs -/

/-- Set of solutions of a CSP with heterogeneous domains -/
def sol_set {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex] 
    (csp : CSP VarIndex DomainType) : Set (Assignment VarIndex DomainType) :=
  { assignment | is_solution csp assignment }

/-! ### Equivalence Relations between CSPs -/

/-- Two CSPs are equivalent if there exists a bijection between their solution sets.
    This generalizes to heterogeneous domains where CSPs can have different variable 
    types and different domain type families. -/
def equivalent {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂] 
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) : Prop :=
  ∃ f : {x // x ∈ sol_set csp₁} → {x // x ∈ sol_set csp₂}, Function.Bijective f

/-- Two CSPs are equisatisfiable if one is satisfiable iff the other is.
    This is a weaker notion than equivalence that only preserves satisfiability.
    Unlike equivalence, equisatisfiability can relate CSPs with different variable
    and domain types. -/
def equisatisfiable {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) : Prop :=
  is_satisfiable csp₁ ↔ is_satisfiable csp₂

/-! ### Projection-based Equivalence (useful for heterogeneous domains) -/

/-- π-equivalence: CSP₂ is π-equivalent to CSP₁ if there exists a projection π
    that maps solutions of CSP₂ bijectively to solutions of CSP₁.
    This is particularly useful when CSP₂ introduces helper variables or
    different domain encodings. -/
def pi_equivalent {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂)
    (π : Assignment VarIndex₂ DomainType₂ → Assignment VarIndex₁ DomainType₁) : Prop :=
  (∀ sol₂ : Assignment VarIndex₂ DomainType₂, is_solution csp₂ sol₂ → is_solution csp₁ (π sol₂)) ∧
  (∀ sol₁ : Assignment VarIndex₁ DomainType₁, is_solution csp₁ sol₁ → 
    ∃ sol₂ : Assignment VarIndex₂ DomainType₂, is_solution csp₂ sol₂ ∧ π sol₂ = sol₁) ∧
  (∀ sol₂ sol₂' : Assignment VarIndex₂ DomainType₂, is_solution csp₂ sol₂ → is_solution csp₂ sol₂' → 
    π sol₂ = π sol₂' → sol₂ = sol₂')

/-! ### Theorems about Equivalence Relations -/

/-- Equivalence implies equisatisfiability -/
theorem equivalent_implies_equisatisfiable {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) :
    equivalent csp₁ csp₂ → equisatisfiable csp₁ csp₂ := by
  intro h
  obtain ⟨f, hf_bij⟩ := h
  have hf_surj : Function.Surjective f := hf_bij.2
  constructor
  · intro h_sat
    obtain ⟨assignment, h_sol⟩ := h_sat
    let y := f ⟨assignment, h_sol⟩
    exact ⟨y.val, y.property⟩
  · intro h_sat'
    obtain ⟨assignment', h_sol'⟩ := h_sat'
    have h_exists : ∃ x, f x = ⟨assignment', h_sol'⟩ := hf_surj ⟨assignment', h_sol'⟩
    obtain ⟨x, hx⟩ := h_exists
    exact ⟨x.val, x.property⟩

/-- π-equivalence implies equisatisfiability -/
theorem pi_equivalent_implies_equisatisfiable {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂)
    (π : Assignment VarIndex₂ DomainType₂ → Assignment VarIndex₁ DomainType₁) :
    pi_equivalent csp₁ csp₂ π → (is_satisfiable csp₁ ↔ is_satisfiable csp₂) := by
  intro h
  obtain ⟨h_forward, h_backward, h_injective⟩ := h
  constructor
  · intro h_sat₁
    obtain ⟨sol₁, h_sol₁⟩ := h_sat₁
    obtain ⟨sol₂, h_sol₂, h_proj⟩ := h_backward sol₁ h_sol₁
    exact ⟨sol₂, h_sol₂⟩
  · intro h_sat₂
    obtain ⟨sol₂, h_sol₂⟩ := h_sat₂
    exact ⟨π sol₂, h_forward sol₂ h_sol₂⟩

/-- π-equivalence implies equivalence -/
theorem pi_equivalent_implies_equivalent {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂)
    (π : Assignment VarIndex₂ DomainType₂ → Assignment VarIndex₁ DomainType₁) :
    pi_equivalent csp₁ csp₂ π → equivalent csp₂ csp₁ := by
  intro h
  obtain ⟨h_forward, h_backward, h_injective⟩ := h
  -- Construct the bijection from the π-equivalence conditions
  let f : {x // x ∈ sol_set csp₂} → {x // x ∈ sol_set csp₁} := 
    fun ⟨sol₂, h_sol₂⟩ => ⟨π sol₂, h_forward sol₂ h_sol₂⟩
  use f
  constructor
  · -- Prove f is injective
    intro ⟨sol₂, h_sol₂⟩ ⟨sol₂', h_sol₂'⟩ h_eq
    -- h_eq : f ⟨sol₂, h_sol₂⟩ = f ⟨sol₂', h_sol₂'⟩
    -- This means ⟨π sol₂, _⟩ = ⟨π sol₂', _⟩, so π sol₂ = π sol₂'
    have h_proj_eq : π sol₂ = π sol₂' := by
      have : (⟨π sol₂, h_forward sol₂ h_sol₂⟩ : {x // x ∈ sol_set csp₁}) = 
             ⟨π sol₂', h_forward sol₂' h_sol₂'⟩ := h_eq
      exact Subtype.mk_eq_mk.mp this
    -- By π-equivalence injectivity condition, sol₂ = sol₂'
    have h_sol_eq : sol₂ = sol₂' := h_injective sol₂ sol₂' h_sol₂ h_sol₂' h_proj_eq
    exact Subtype.ext h_sol_eq
  · -- Prove f is surjective
    intro ⟨sol₁, h_sol₁⟩
    -- By π-equivalence backward condition, there exists sol₂ that projects to sol₁
    obtain ⟨sol₂, h_sol₂, h_proj⟩ := h_backward sol₁ h_sol₁
    use ⟨sol₂, h_sol₂⟩
    -- Show f maps this sol₂ to sol₁
    simp only [f]
    exact Subtype.ext h_proj

/-! ### Equivalence Relations are Reflexive, Symmetric, and Transitive -/

/-- Equivalence is reflexive -/
theorem equivalent_refl {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) : equivalent csp csp := by
  use id
  exact Function.bijective_id

/-- Equivalence is symmetric -/
theorem equivalent_symm {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) :
    equivalent csp₁ csp₂ → equivalent csp₂ csp₁ := by
  intro h
  obtain ⟨f, hf_bij⟩ := h
  use Function.surjInv hf_bij.2
  constructor
  · exact Function.injective_surjInv hf_bij.2
  · -- Prove surjInv is surjective for bijective functions
    -- Use the fact that leftInverse_surjInv gives us LeftInverse (surjInv _) f
    have h_left : Function.LeftInverse (Function.surjInv hf_bij.2) f := 
      Function.leftInverse_surjInv hf_bij
    -- For any element a in the domain, f a serves as a preimage
    intro a
    use f a
    exact h_left a

/-- Equivalence is transitive -/
theorem equivalent_trans {VarIndex₁ VarIndex₂ VarIndex₃ : Type} 
    {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type} {DomainType₃ : VarIndex₃ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂] [DecidableEq VarIndex₃]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) (csp₃ : CSP VarIndex₃ DomainType₃) :
    equivalent csp₁ csp₂ → equivalent csp₂ csp₃ → equivalent csp₁ csp₃ := by
  intro h₁₂ h₂₃
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  use f₂₃ ∘ f₁₂
  exact Function.Bijective.comp hf₂₃ hf₁₂

/-- Equisatisfiability is reflexive -/
theorem equisatisfiable_refl {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp : CSP VarIndex DomainType) : equisatisfiable csp csp := by
  rfl

/-- Equisatisfiability is symmetric -/
theorem equisatisfiable_symm {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) :
    equisatisfiable csp₁ csp₂ → equisatisfiable csp₂ csp₁ := by
  intro h
  exact h.symm

/-- Equisatisfiability is transitive -/
theorem equisatisfiable_trans {VarIndex₁ VarIndex₂ VarIndex₃ : Type} 
    {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type} {DomainType₃ : VarIndex₃ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂] [DecidableEq VarIndex₃]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) (csp₃ : CSP VarIndex₃ DomainType₃) :
    equisatisfiable csp₁ csp₂ → equisatisfiable csp₂ csp₃ → equisatisfiable csp₁ csp₃ := by
  intro h₁₂ h₂₃
  exact h₁₂.trans h₂₃

/-! ### Homogeneous Domain Equivalence (special case) -/

/-- For CSPs with the same variable and domain types, we can define a simpler
    equivalence relation that directly compares solution sets -/
def homogeneous_equivalent {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp₁ csp₂ : CSP VarIndex DomainType) : Prop :=
  ∀ assignment : Assignment VarIndex DomainType,
    is_solution csp₁ assignment ↔ is_solution csp₂ assignment

/-- Homogeneous equivalence implies general equivalence -/
theorem homogeneous_equivalent_implies_equivalent {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp₁ csp₂ : CSP VarIndex DomainType) :
    homogeneous_equivalent csp₁ csp₂ → equivalent csp₁ csp₂ := by
  intro h
  -- Create a bijection based on the fact that solution sets are equal
  let f : {x // x ∈ sol_set csp₁} → {x // x ∈ sol_set csp₂} := 
    fun ⟨x, hx⟩ => ⟨x, (h x).1 hx⟩
  use f
  constructor
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    -- hab : f ⟨a, ha⟩ = f ⟨b, hb⟩
    -- f ⟨a, ha⟩ = ⟨a, (h a).1 ha⟩ and f ⟨b, hb⟩ = ⟨b, (h b).1 hb⟩
    have h_eq : a = b := by
      have : (⟨a, (h a).1 ha⟩ : {x // x ∈ sol_set csp₂}) = ⟨b, (h b).1 hb⟩ := hab
      exact Subtype.mk_eq_mk.mp this
    exact Subtype.ext h_eq
  · intro ⟨b, hb⟩
    use ⟨b, (h b).2 hb⟩

/-! ### Utility Lemmas -/

/-- If two CSPs have the same solution set, they are equivalent -/
theorem sol_set_eq_implies_equivalent {VarIndex : Type} {DomainType : VarIndex → Type} [DecidableEq VarIndex]
    (csp₁ csp₂ : CSP VarIndex DomainType) :
    sol_set csp₁ = sol_set csp₂ → equivalent csp₁ csp₂ := by
  intro h
  -- Create a bijection based on the equality of solution sets
  let f : {x // x ∈ sol_set csp₁} → {x // x ∈ sol_set csp₂} := 
    fun ⟨x, hx⟩ => ⟨x, h ▸ hx⟩
  use f
  constructor
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    -- Both solution sets are equal, so if f maps them to the same element, 
    -- the original elements must be equal
    have h_eq : a = b := by
      have : (⟨a, h ▸ ha⟩ : {x // x ∈ sol_set csp₂}) = ⟨b, h ▸ hb⟩ := hab
      exact Subtype.mk_eq_mk.mp this
    exact Subtype.ext h_eq
  · intro ⟨b, hb⟩
    use ⟨b, h ▸ hb⟩

/-- Empty solution sets are equivalent -/
theorem empty_sol_set_equivalent {VarIndex₁ VarIndex₂ : Type} {DomainType₁ : VarIndex₁ → Type} {DomainType₂ : VarIndex₂ → Type}
    [DecidableEq VarIndex₁] [DecidableEq VarIndex₂]
    (csp₁ : CSP VarIndex₁ DomainType₁) (csp₂ : CSP VarIndex₂ DomainType₂) :
    sol_set csp₁ = ∅ → sol_set csp₂ = ∅ → equivalent csp₁ csp₂ := by
  intro h₁ h₂
  -- Both solution sets are empty, so any function between them is bijective
  let f : {x // x ∈ sol_set csp₁} → {x // x ∈ sol_set csp₂} := 
    fun ⟨x, hx⟩ => by 
      rw [h₁] at hx
      exact False.elim hx
  use f
  constructor
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    rw [h₁] at ha
    exact False.elim ha
  · intro ⟨b, hb⟩
    rw [h₂] at hb
    exact False.elim hb

end CSP