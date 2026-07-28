import CSP.L2S.Core
import CSP.L2S.Embedding
import CSP.Equivalence
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Basic

namespace CSP.L2S

/-!
# L2S equivalence theory

Equivalence relations between `IntCSP`s, in decreasing strength:

```
π-equivalence ⟹ Strong equivalence ⟹ Equisatisfiability
   (bijection)     (same solutions)    (both SAT or UNSAT)
```
-/

open IntCSP

/-! ### Solution Set Definition -/

/-- The solution set for an L2S CSP with integer domains -/
def solSet (csp : IntCSP) : Set (IntAssignment csp.num_vars) :=
  { assignment | isSolutionInt csp assignment }

/-- Solution set equals heterogeneous counterpart via embedding -/
theorem solSet_eq_heterogeneous (csp : IntCSP) :
    solSet csp = CSP.sol_set (embed csp) := by
  ext assignment
  simp only [solSet, CSP.sol_set, Set.mem_setOf]
  exact embedding_preserves_solutions csp assignment

/-! ### Native Equivalence Relations -/

/--
Two L2S CSPs are equivalent if there exists a bijection between their solution sets.
This is the strongest equivalence notion.
-/
def equivalent (csp₁ csp₂ : IntCSP) : Prop :=
  ∃ f : {x // x ∈ solSet csp₁} → {x // x ∈ solSet csp₂}, Function.Bijective f

/--
Two L2S CSPs are equisatisfiable if they have the same satisfiability status.
This is a weaker notion than equivalence.
-/
def equisatisfiable (csp₁ csp₂ : IntCSP) : Prop :=
  isSatisfiableInt csp₁ ↔ isSatisfiableInt csp₂

/--
π-equivalence: CSP₂ is π-equivalent to CSP₁ via projection π if:
1. Every solution of csp₂ projects to a solution of csp₁
2. Every solution of csp₁ has a preimage solution in csp₂
3. Different csp₂ solutions project to different csp₁ solutions
-/
def piEquivalent (csp₁ csp₂ : IntCSP)
    (π : IntAssignment csp₂.num_vars → IntAssignment csp₁.num_vars) : Prop :=
  (∀ sol₂ : IntAssignment csp₂.num_vars,
    isSolutionInt csp₂ sol₂ → isSolutionInt csp₁ (π sol₂)) ∧
  (∀ sol₁ : IntAssignment csp₁.num_vars,
    isSolutionInt csp₁ sol₁ →
    ∃ sol₂ : IntAssignment csp₂.num_vars,
      isSolutionInt csp₂ sol₂ ∧ π sol₂ = sol₁) ∧
  (∀ sol₂ sol₂' : IntAssignment csp₂.num_vars,
    isSolutionInt csp₂ sol₂ → isSolutionInt csp₂ sol₂' →
    π sol₂ = π sol₂' → sol₂ = sol₂')

/-! ### Equivalence Hierarchy -/

/-- π-equivalence implies equivalence -/
theorem piEquivalent_implies_equivalent (csp₁ csp₂ : IntCSP)
    (π : IntAssignment csp₂.num_vars → IntAssignment csp₁.num_vars) :
    piEquivalent csp₁ csp₂ π → equivalent csp₂ csp₁ := by
  intro h
  obtain ⟨h_forward, h_backward, h_injective⟩ := h
  let f : {x // x ∈ solSet csp₂} → {x // x ∈ solSet csp₁} :=
    fun ⟨sol₂, h_sol₂⟩ => ⟨π sol₂, h_forward sol₂ h_sol₂⟩
  use f
  constructor
  · -- Injective
    intro ⟨sol₂, h_sol₂⟩ ⟨sol₂', h_sol₂'⟩ h_eq
    have h_proj_eq : π sol₂ = π sol₂' := by
      have : (⟨π sol₂, h_forward sol₂ h_sol₂⟩ : {x // x ∈ solSet csp₁}) =
             ⟨π sol₂', h_forward sol₂' h_sol₂'⟩ := h_eq
      exact Subtype.mk_eq_mk.mp this
    have h_sol_eq : sol₂ = sol₂' := h_injective sol₂ sol₂' h_sol₂ h_sol₂' h_proj_eq
    exact Subtype.ext h_sol_eq
  · -- Surjective
    intro ⟨sol₁, h_sol₁⟩
    obtain ⟨sol₂, h_sol₂, h_proj⟩ := h_backward sol₁ h_sol₁
    use ⟨sol₂, h_sol₂⟩
    simp only [f]
    exact Subtype.ext h_proj

/-- Equivalence implies equisatisfiability -/
theorem equivalent_implies_equisatisfiable (csp₁ csp₂ : IntCSP) :
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
    obtain ⟨x, _⟩ := h_exists
    exact ⟨x.val, x.property⟩

/-- π-equivalence implies equisatisfiability -/
theorem piEquivalent_implies_equisatisfiable (csp₁ csp₂ : IntCSP)
    (π : IntAssignment csp₂.num_vars → IntAssignment csp₁.num_vars) :
    piEquivalent csp₁ csp₂ π → equisatisfiable csp₁ csp₂ := by
  intro h
  have h_equiv := piEquivalent_implies_equivalent csp₁ csp₂ π h
  have h_equisat := equivalent_implies_equisatisfiable csp₂ csp₁ h_equiv
  exact h_equisat.symm

/-! ### Equivalence Properties (Reflexivity, Symmetry, Transitivity) -/

/-- Equivalence is reflexive -/
theorem equivalent_refl (csp : IntCSP) : equivalent csp csp := by
  use id
  exact Function.bijective_id

/-- Equivalence is symmetric -/
theorem equivalent_symm (csp₁ csp₂ : IntCSP) :
    equivalent csp₁ csp₂ → equivalent csp₂ csp₁ := by
  intro h
  obtain ⟨f, hf_bij⟩ := h
  use Function.surjInv hf_bij.2
  constructor
  · exact Function.injective_surjInv hf_bij.2
  · have h_left : Function.LeftInverse (Function.surjInv hf_bij.2) f :=
      Function.leftInverse_surjInv hf_bij
    intro a
    use f a
    exact h_left a

/-- Equivalence is transitive -/
theorem equivalent_trans (csp₁ csp₂ csp₃ : IntCSP) :
    equivalent csp₁ csp₂ → equivalent csp₂ csp₃ → equivalent csp₁ csp₃ := by
  intro h₁₂ h₂₃
  obtain ⟨f₁₂, hf₁₂⟩ := h₁₂
  obtain ⟨f₂₃, hf₂₃⟩ := h₂₃
  use f₂₃ ∘ f₁₂
  exact Function.Bijective.comp hf₂₃ hf₁₂

/-- Equisatisfiability is reflexive -/
theorem equisatisfiable_refl (csp : IntCSP) : equisatisfiable csp csp := by
  rfl

/-- Equisatisfiability is symmetric -/
theorem equisatisfiable_symm (csp₁ csp₂ : IntCSP) :
    equisatisfiable csp₁ csp₂ → equisatisfiable csp₂ csp₁ := by
  intro h
  exact h.symm

/-- Equisatisfiability is transitive -/
theorem equisatisfiable_trans (csp₁ csp₂ csp₃ : IntCSP) :
    equisatisfiable csp₁ csp₂ → equisatisfiable csp₂ csp₃ → equisatisfiable csp₁ csp₃ := by
  intro h₁₂ h₂₃
  exact h₁₂.trans h₂₃

/-! ### Compatibility with Heterogeneous Equivalence -/

/-- L2S equisatisfiability implies heterogeneous equisatisfiability via embedding -/
theorem equisatisfiable_implies_heterogeneous_equisatisfiable (csp₁ csp₂ : IntCSP) :
    equisatisfiable csp₁ csp₂ → CSP.equisatisfiable (embed csp₁) (embed csp₂) := by
  intro h
  simp only [CSP.equisatisfiable]
  rw [← embedding_preserves_satisfiability csp₁]
  rw [← embedding_preserves_satisfiability csp₂]
  exact h

/-- Heterogeneous equisatisfiability implies L2S equisatisfiability (converse) -/
theorem heterogeneous_equisatisfiable_implies_equisatisfiable (csp₁ csp₂ : IntCSP) :
    CSP.equisatisfiable (embed csp₁) (embed csp₂) → equisatisfiable csp₁ csp₂ := by
  intro h
  simp only [CSP.equisatisfiable] at h
  simp only [equisatisfiable]
  exact (embedding_preserves_satisfiability csp₁).trans
    (h.trans (embedding_preserves_satisfiability csp₂).symm)

/-- L2S equisatisfiability is equivalent to heterogeneous equisatisfiability -/
theorem equisatisfiable_iff_heterogeneous_equisatisfiable (csp₁ csp₂ : IntCSP) :
    equisatisfiable csp₁ csp₂ ↔ CSP.equisatisfiable (embed csp₁) (embed csp₂) := by
  constructor
  · exact equisatisfiable_implies_heterogeneous_equisatisfiable csp₁ csp₂
  · exact heterogeneous_equisatisfiable_implies_equisatisfiable csp₁ csp₂

/-- L2S equivalence implies heterogeneous equivalence via embedding -/
theorem equivalent_implies_heterogeneous_equivalent (csp₁ csp₂ : IntCSP) :
    equivalent csp₁ csp₂ → CSP.equivalent (embed csp₁) (embed csp₂) := by
  intro h
  obtain ⟨f, hf_bij⟩ := h
  -- Construct bijection between heterogeneous solution sets
  let g : {x // x ∈ CSP.sol_set (embed csp₁)} → {x // x ∈ CSP.sol_set (embed csp₂)} :=
    fun ⟨x, hx⟩ => by
      have hx' : x ∈ solSet csp₁ := (solSet_eq_heterogeneous csp₁).symm ▸ hx
      let y := f ⟨x, hx'⟩
      have hy : y.val ∈ CSP.sol_set (embed csp₂) := solSet_eq_heterogeneous csp₂ ▸ y.property
      exact ⟨y.val, hy⟩
  use g
  constructor
  · -- Injective
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [g] at hab
    have ha' : a ∈ solSet csp₁ := (solSet_eq_heterogeneous csp₁).symm ▸ ha
    have hb' : b ∈ solSet csp₁ := (solSet_eq_heterogeneous csp₁).symm ▸ hb
    have h_eq_vals : (f ⟨a, ha'⟩).val = (f ⟨b, hb'⟩).val := Subtype.mk_eq_mk.mp hab
    have h_eq_subtypes : f ⟨a, ha'⟩ = f ⟨b, hb'⟩ := Subtype.ext h_eq_vals
    have h_inj := hf_bij.1 h_eq_subtypes
    have h_a_eq_b : a = b := Subtype.mk_eq_mk.mp h_inj
    exact Subtype.ext h_a_eq_b
  · -- Surjective
    intro ⟨b, hb⟩
    have hb' : b ∈ solSet csp₂ := (solSet_eq_heterogeneous csp₂).symm ▸ hb
    have : ∃ x, f x = ⟨b, hb'⟩ := hf_bij.2 ⟨b, hb'⟩
    obtain ⟨⟨a, ha⟩, heq⟩ := this
    have ha_het : a ∈ CSP.sol_set (embed csp₁) := solSet_eq_heterogeneous csp₁ ▸ ha
    use ⟨a, ha_het⟩
    simp only [g]
    apply Subtype.ext
    have h_val_eq : (f ⟨a, ha⟩).val = b := Subtype.mk_eq_mk.mp heq
    exact h_val_eq

/-- Heterogeneous equivalence implies L2S equivalence (converse) -/
theorem heterogeneous_equivalent_implies_equivalent (csp₁ csp₂ : IntCSP) :
    CSP.equivalent (embed csp₁) (embed csp₂) → equivalent csp₁ csp₂ := by
  intro h
  obtain ⟨f, hf_bij⟩ := h
  -- Construct bijection between L2S solution sets
  let g : {x // x ∈ solSet csp₁} → {x // x ∈ solSet csp₂} :=
    fun ⟨x, hx⟩ => by
      have hx' : x ∈ CSP.sol_set (embed csp₁) := solSet_eq_heterogeneous csp₁ ▸ hx
      let y := f ⟨x, hx'⟩
      have hy : y.val ∈ solSet csp₂ := (solSet_eq_heterogeneous csp₂).symm ▸ y.property
      exact ⟨y.val, hy⟩
  use g
  constructor
  · -- Injective
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [g] at hab
    have ha' : a ∈ CSP.sol_set (embed csp₁) := solSet_eq_heterogeneous csp₁ ▸ ha
    have hb' : b ∈ CSP.sol_set (embed csp₁) := solSet_eq_heterogeneous csp₁ ▸ hb
    have h_eq_vals : (f ⟨a, ha'⟩).val = (f ⟨b, hb'⟩).val := Subtype.mk_eq_mk.mp hab
    have h_eq_subtypes : f ⟨a, ha'⟩ = f ⟨b, hb'⟩ := Subtype.ext h_eq_vals
    have h_inj := hf_bij.1 h_eq_subtypes
    have h_a_eq_b : a = b := Subtype.mk_eq_mk.mp h_inj
    exact Subtype.ext h_a_eq_b
  · -- Surjective
    intro ⟨b, hb⟩
    have hb' : b ∈ CSP.sol_set (embed csp₂) := solSet_eq_heterogeneous csp₂ ▸ hb
    have : ∃ x, f x = ⟨b, hb'⟩ := hf_bij.2 ⟨b, hb'⟩
    obtain ⟨⟨a, ha⟩, heq⟩ := this
    have ha_hom : a ∈ solSet csp₁ := (solSet_eq_heterogeneous csp₁).symm ▸ ha
    use ⟨a, ha_hom⟩
    simp only [g]
    apply Subtype.ext
    have h_val_eq : (f ⟨a, ha⟩).val = b := Subtype.mk_eq_mk.mp heq
    exact h_val_eq

/-- L2S equivalence is equivalent to heterogeneous equivalence -/
theorem equivalent_iff_heterogeneous_equivalent (csp₁ csp₂ : IntCSP) :
    equivalent csp₁ csp₂ ↔ CSP.equivalent (embed csp₁) (embed csp₂) := by
  constructor
  · exact equivalent_implies_heterogeneous_equivalent csp₁ csp₂
  · exact heterogeneous_equivalent_implies_equivalent csp₁ csp₂

end CSP.L2S
