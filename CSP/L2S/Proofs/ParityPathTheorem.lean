import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Proofs.UnreachableInputElimination
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Bool.Basic

namespace CSP.L2S

open HomogeneousCSP

/-!
# Parity Path Theorem (Pure Literal Rule for Circuits)

This module proves that circuit inputs where ALL paths to ALL outputs have the
SAME parity can be fixed to an optimal value without affecting satisfiability.

## Key Insight

- **Even parity** (0 NOT gates mod 2): Input appears "positively" → fix to 1
- **Odd parity** (1 NOT gate mod 2): Input appears "negatively" → fix to 0

## Scope

This theorem applies to **AND/OR/NOT circuits only**. XOR gates break monotonicity
and require separate treatment (e.g., linear algebra over GF(2)).

## Main Results

1. `ParityReaches` - Inductive path relation with parity accumulator
2. `UniformParity` - All paths from input to node have same parity
3. `value_monotone_fuel` - Coincidence lemma with monotonicity
4. `uniform_parity_pure_literal` - Main theorem: fixing input preserves SAT

## Connection to Classical Theory

- **Unate functions**: Boolean functions monotone in each variable
- **Parity graphs**: All paths between vertices have same length parity
- **Pure literal rule**: CNF literal with single polarity can be fixed
-/

-- ============================================================================
-- Gate Parity Classification
-- ============================================================================

/-- Whether a gate type flips the parity (inverts the signal). -/
def gate_parity_flip (gt : GateType) : Bool :=
  match gt with
  | .NOT => true
  | .XOR => true
  | .AND => false
  | .OR  => false

/-- A circuit is monotone if it contains no XOR gates. -/
def circuit_is_monotone (c : Circuit) : Prop :=
  ∀ g ∈ c.gates, g.gate_type ≠ GateType.XOR

-- ============================================================================
-- Parity-Tracked Reachability
-- ============================================================================

/-- Direct edge with parity: src feeds into tgt via gate g with parity delta. -/
def DirectParity (c : Circuit) (src tgt : ℕ) (delta : Bool) : Prop :=
  ∃ g ∈ c.gates, src ∈ g.inputs ∧ g.output = tgt ∧ delta = gate_parity_flip g.gate_type

/-- Inductive definition of reachability with accumulated parity. -/
inductive ParityReaches (c : Circuit) : ℕ → ℕ → Bool → Prop where
  | refl (v : ℕ) : ParityReaches c v v false
  | step (src mid tgt : ℕ) (p_acc : Bool) (p_edge : Bool)
      (h_path : ParityReaches c src mid p_acc)
      (h_edge : DirectParity c mid tgt p_edge) :
      ParityReaches c src tgt (xor p_acc p_edge)

/-- There exists some path from src to tgt (with any parity). -/
def ParityReachesAny (c : Circuit) (src tgt : ℕ) : Prop :=
  ∃ p, ParityReaches c src tgt p

-- ============================================================================
-- Uniform Parity Definition
-- ============================================================================

/-- Uniform parity to a specific node: reachable, and ALL paths have parity p. -/
def UniformParityTo (c : Circuit) (src tgt : ℕ) (p : Bool) : Prop :=
  (∃ q, ParityReaches c src tgt q) ∧ (∀ q, ParityReaches c src tgt q → q = p)

/-- Input i reaches some output with tracked parity. -/
def parity_reaches_output (c : Circuit) (i : ℕ) : Prop :=
  ∃ out, is_output c out ∧ ParityReachesAny c i out

/-- All paths from input i to ALL outputs have the same parity p. -/
def UniformParity (c : Circuit) (i : ℕ) (p : Bool) : Prop :=
  parity_reaches_output c i ∧
  ∀ out, is_output c out → ∀ q, ParityReaches c i out q → q = p

-- ============================================================================
-- Monotonicity Predicate
-- ============================================================================

/-- Monotonicity relationship between two Boolean values given a parity. -/
def is_monotone (val0 val1 : Bool) (parity : Bool) : Prop :=
  if parity then (val1 = true → val0 = true)
  else (val0 = true → val1 = true)

-- ============================================================================
-- Helper Lemmas
-- ============================================================================

lemma parity_refl_is_false (c : Circuit) (v : ℕ) :
    ParityReaches c v v false := ParityReaches.refl v

lemma parity_reaches_any_of_reaches (c : Circuit) (src tgt : ℕ) (p : Bool)
    (h : ParityReaches c src tgt p) : ParityReachesAny c src tgt :=
  ⟨p, h⟩

lemma is_monotone_of_eq (val : Bool) (parity : Bool) :
    is_monotone val val parity := by
  unfold is_monotone; split_ifs <;> simp

lemma update_eq_self {α β : Type*} [DecidableEq α] (f : α → β) (a : α) :
    Function.update f a (f a) = f := by
  ext x; by_cases hx : x = a <;> simp [Function.update, hx]

lemma update_eq_self_of_eq {α β : Type*} [DecidableEq α] (f : α → β) (a : α) (v : β)
    (hv : f a = v) : Function.update f a v = f := by
  subst hv; exact update_eq_self f a

lemma not_gate_monotone (val0 val1 : Bool) (p : Bool)
    (h : is_monotone val0 val1 p) :
    is_monotone (!val0) (!val1) (!p) := by
  unfold is_monotone at *
  cases p <;> cases val0 <;> cases val1 <;> simp_all

-- ============================================================================
-- Per-Gate Monotonicity (Proven)
-- ============================================================================

private lemma and_gate_monotone_false (inputs0 inputs1 : List Bool)
    (h_len : inputs0.length = inputs1.length)
    (h_mono : ∀ k : Nat, k < inputs0.length → (inputs0[k]! = true → inputs1[k]! = true)) :
    inputs0.all id = true → inputs1.all id = true := by
  intro h_all0
  rw [List.all_eq_true] at *
  intro x hx
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx
  have h_n_lt1 : n.val < inputs1.length := n.isLt
  have h_n_lt0 : n.val < inputs0.length := by omega
  have h_mono_n := h_mono n.val h_n_lt0
  rw [← hn, List.get_eq_getElem]
  simp only [id_eq]
  rw [← getElem!_pos inputs1 n.val h_n_lt1]
  apply h_mono_n
  rw [getElem!_pos inputs0 n.val h_n_lt0]
  have hmem : inputs0[n.val] ∈ inputs0 := List.getElem_mem h_n_lt0
  have := h_all0 inputs0[n.val] hmem
  simp only [id_eq] at this
  exact this

private lemma and_gate_monotone_true (inputs0 inputs1 : List Bool)
    (h_len : inputs0.length = inputs1.length)
    (h_mono : ∀ k : Nat, k < inputs0.length → (inputs1[k]! = true → inputs0[k]! = true)) :
    inputs1.all id = true → inputs0.all id = true := by
  intro h_all1
  rw [List.all_eq_true] at *
  intro x hx
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx
  have h_n_lt0 : n.val < inputs0.length := n.isLt
  have h_n_lt1 : n.val < inputs1.length := by omega
  have h_mono_n := h_mono n.val h_n_lt0
  rw [← hn, List.get_eq_getElem]
  simp only [id_eq]
  rw [← getElem!_pos inputs0 n.val h_n_lt0]
  apply h_mono_n
  rw [getElem!_pos inputs1 n.val h_n_lt1]
  have hmem : inputs1[n.val] ∈ inputs1 := List.getElem_mem h_n_lt1
  have := h_all1 inputs1[n.val] hmem
  simp only [id_eq] at this
  exact this

private lemma or_gate_monotone_false (inputs0 inputs1 : List Bool)
    (h_len : inputs0.length = inputs1.length)
    (h_mono : ∀ k : Nat, k < inputs0.length → (inputs0[k]! = true → inputs1[k]! = true)) :
    inputs0.any id = true → inputs1.any id = true := by
  intro h_any0
  rw [List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_true⟩ := h_any0
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx_mem
  have h_n_lt0 : n.val < inputs0.length := n.isLt
  have h_n_lt1 : n.val < inputs1.length := by omega
  have h_mono_n := h_mono n.val h_n_lt0
  refine ⟨inputs1[n.val], List.getElem_mem h_n_lt1, ?_⟩
  simp only [id_eq]
  rw [← getElem!_pos inputs1 n.val h_n_lt1]
  apply h_mono_n
  rw [getElem!_pos inputs0 n.val h_n_lt0, ← List.get_eq_getElem, hn]
  simp only [id_eq] at hx_true
  exact hx_true

private lemma or_gate_monotone_true (inputs0 inputs1 : List Bool)
    (h_len : inputs0.length = inputs1.length)
    (h_mono : ∀ k : Nat, k < inputs0.length → (inputs1[k]! = true → inputs0[k]! = true)) :
    inputs1.any id = true → inputs0.any id = true := by
  intro h_any1
  rw [List.any_eq_true] at *
  obtain ⟨x, hx_mem, hx_true⟩ := h_any1
  obtain ⟨n, hn⟩ := List.mem_iff_get.mp hx_mem
  have h_n_lt1 : n.val < inputs1.length := n.isLt
  have h_n_lt0 : n.val < inputs0.length := by omega
  have h_mono_n := h_mono n.val h_n_lt0
  refine ⟨inputs0[n.val], List.getElem_mem h_n_lt0, ?_⟩
  simp only [id_eq]
  rw [← getElem!_pos inputs0 n.val h_n_lt0]
  apply h_mono_n
  rw [getElem!_pos inputs1 n.val h_n_lt1, ← List.get_eq_getElem, hn]
  simp only [id_eq] at hx_true
  exact hx_true

/-- AND gate preserves monotonicity across all inputs. -/
lemma and_gate_monotone :
    ∀ (inputs0 inputs1 : List Bool) (p : Bool),
    inputs0.length = inputs1.length →
    (∀ k : ℕ, k < inputs0.length → is_monotone (inputs0[k]!) (inputs1[k]!) p) →
    is_monotone (inputs0.all id) (inputs1.all id) p := by
  intro inputs0 inputs1 p h_len h_mono
  unfold is_monotone at *
  cases p with
  | false => exact and_gate_monotone_false inputs0 inputs1 h_len h_mono
  | true => exact and_gate_monotone_true inputs0 inputs1 h_len h_mono

/-- OR gate preserves monotonicity across all inputs. -/
lemma or_gate_monotone :
    ∀ (inputs0 inputs1 : List Bool) (p : Bool),
    inputs0.length = inputs1.length →
    (∀ k : ℕ, k < inputs0.length → is_monotone (inputs0[k]!) (inputs1[k]!) p) →
    is_monotone (inputs0.any id) (inputs1.any id) p := by
  intro inputs0 inputs1 p h_len h_mono
  unfold is_monotone at *
  cases p with
  | false => exact or_gate_monotone_false inputs0 inputs1 h_len h_mono
  | true => exact or_gate_monotone_true inputs0 inputs1 h_len h_mono

-- ============================================================================
-- Connecting Reaches to ParityReaches
-- ============================================================================

lemma direct_parity_of_direct_dep (c : Circuit) (src tgt : ℕ)
    (h : DirectDependency c src tgt) :
    ∃ delta, DirectParity c src tgt delta := by
  obtain ⟨g, h_g_mem, h_src_in, h_out_eq⟩ := h
  exact ⟨gate_parity_flip g.gate_type, g, h_g_mem, h_src_in, h_out_eq, rfl⟩

lemma parity_reaches_any_of_reaches' (c : Circuit) (src tgt : ℕ)
    (h : Reaches c src tgt) : ParityReachesAny c src tgt := by
  induction h with
  | single h_direct =>
    obtain ⟨delta, h_parity⟩ := direct_parity_of_direct_dep c src _ h_direct
    exact ⟨xor false delta, ParityReaches.step src src _ false delta (ParityReaches.refl src) h_parity⟩
  | tail _h_reach h_edge ih =>
    obtain ⟨p, h_path⟩ := ih
    obtain ⟨delta, h_parity⟩ := direct_parity_of_direct_dep c _ _ h_edge
    exact ⟨xor p delta, ParityReaches.step src _ _ p delta h_path h_parity⟩

lemma parity_reaches_any_of_reaches_or_eq (c : Circuit) (src tgt : ℕ)
    (h : ReachesOrEq c src tgt) : ParityReachesAny c src tgt := by
  cases h with
  | inl h_eq => exact ⟨false, h_eq ▸ ParityReaches.refl src⟩
  | inr h_reaches => exact parity_reaches_any_of_reaches' c src tgt h_reaches

-- ============================================================================
-- Core Monotonicity Theorem (Proven)
-- ============================================================================

/-- If i reaches tgt with uniform parity p, and src feeds tgt with parity delta,
    then i reaches src with uniform parity (xor p delta) (if reachable). -/
lemma uniform_parity_predecessor (c : Circuit) (i src tgt : ℕ) (p delta : Bool)
    (h_uniform : UniformParityTo c i tgt p)
    (h_edge : DirectParity c src tgt delta)
    (h_reach_src : ParityReachesAny c i src) :
    UniformParityTo c i src (xor p delta) := by
  obtain ⟨_, h_all_paths⟩ := h_uniform
  constructor
  · exact h_reach_src
  · intro q h_q
    have h_path_tgt : ParityReaches c i tgt (xor q delta) :=
      ParityReaches.step i src tgt q delta h_q h_edge
    have h_eq := h_all_paths (xor q delta) h_path_tgt
    cases q <;> cases delta <;> cases p <;> simp_all

/-- The parity from i to i is false (zero-length path). -/
lemma uniform_parity_self (c : Circuit) (i : ℕ) (p : Bool)
    (h_uniform : UniformParityTo c i i p) : p = false := by
  obtain ⟨_, h_all⟩ := h_uniform
  exact (h_all false (ParityReaches.refl i)).symm

/-- Key lemma: If input i has uniform parity p to node v in a monotone circuit,
    then flipping i preserves the monotonicity relationship at v. -/
theorem value_monotone_fuel
    (c : Circuit)
    (h_strict : circuit_strictly_ordered c)
    (h_mono_circuit : circuit_is_monotone c)
    (i : ℕ) (h_i_input : i < c.num_inputs)
    (fuel : ℕ) (v : ℕ) (p : Bool)
    (h_uniform : UniformParityTo c i v p) :
    ∀ assignment : ℕ → Bool,
      is_monotone
        (eval_node_fuel c (Function.update assignment i false) fuel v)
        (eval_node_fuel c (Function.update assignment i true) fuel v)
        p := by
  induction fuel generalizing v p with
  | zero =>
    intro _
    simp only [eval_node_fuel]
    exact is_monotone_of_eq false p
  | succ fuel ih =>
    intro assignment
    simp only [eval_node_fuel]
    by_cases hv_in : v < c.num_inputs
    · simp only [hv_in, ↓reduceIte]
      by_cases h_eq : v = i
      · have h_p_false : p = false := by
          rw [h_eq] at h_uniform
          exact uniform_parity_self c i p h_uniform
        subst h_eq h_p_false
        simp only [Function.update]
        simp only [is_monotone]
        intro _; rfl
      · have h_neq : v ≠ i := h_eq
        simp only [Function.update, h_neq]
        exact is_monotone_of_eq (assignment v) p
    · simp only [hv_in, ↓reduceIte]
      cases h_gate : find_gate_for_output c v with
      | none => exact is_monotone_of_eq false p
      | some g =>
        have h_g_mem : g ∈ c.gates := find_gate_mem c v g h_gate
        have h_g_out : g.output = v := find_gate_output_eq c v g h_gate
        have h_no_xor : g.gate_type ≠ GateType.XOR := h_mono_circuit g h_g_mem
        let delta := gate_parity_flip g.gate_type
        let inputs0 := g.inputs.map (eval_node_fuel c (Function.update assignment i false) fuel)
        let inputs1 := g.inputs.map (eval_node_fuel c (Function.update assignment i true) fuel)
        have h_inputs_len : inputs0.length = inputs1.length := by simp [inputs0, inputs1]
        have h_inputs_mono : ∀ k : ℕ, k < inputs0.length →
            is_monotone (inputs0[k]!) (inputs1[k]!) (xor p delta) := by
          intro k hk
          have hk' : k < g.inputs.length := by simp [inputs0] at hk; exact hk
          have hk0 : k < inputs0.length := hk
          have hk1 : k < inputs1.length := by simp [inputs1]; exact hk'
          by_cases h_reach_u : ParityReachesAny c i (g.inputs[k])
          · have h_edge_u : DirectParity c (g.inputs[k]) v delta := by
              use g, h_g_mem
              constructor
              · exact List.getElem_mem hk'
              · exact ⟨h_g_out, rfl⟩
            have h_uni_u := uniform_parity_predecessor c i (g.inputs[k]) v p delta h_uniform h_edge_u h_reach_u
            have h_ih := ih (g.inputs[k]) (xor p delta) h_uni_u assignment
            rw [getElem!_pos inputs0 k hk0, getElem!_pos inputs1 k hk1]
            simp only [inputs0, inputs1, List.getElem_map]
            exact h_ih
          · have h_no_path : ¬ReachesOrEq c i (g.inputs[k]) := fun h_r =>
              h_reach_u (parity_reaches_any_of_reaches_or_eq c i (g.inputs[k]) h_r)
            have h_eq_val := value_independent_of_unreachable_fuel c h_strict i h_i_input
              fuel (g.inputs[k]) h_no_path assignment
            rw [getElem!_pos inputs0 k hk0, getElem!_pos inputs1 k hk1]
            simp only [inputs0, inputs1, List.getElem_map]
            rw [h_eq_val]
            exact is_monotone_of_eq _ _
        cases hgt : g.gate_type with
        | AND =>
          simp only [eval_gate_op, hgt]
          have h_delta : delta = false := by simp [delta, gate_parity_flip, hgt]
          rw [h_delta, Bool.xor_false] at h_inputs_mono
          exact and_gate_monotone inputs0 inputs1 p h_inputs_len h_inputs_mono
        | OR =>
          simp only [eval_gate_op, hgt]
          have h_delta : delta = false := by simp [delta, gate_parity_flip, hgt]
          rw [h_delta, Bool.xor_false] at h_inputs_mono
          exact or_gate_monotone inputs0 inputs1 p h_inputs_len h_inputs_mono
        | XOR =>
          exact absurd hgt h_no_xor
        | NOT =>
          simp only [eval_gate_op, hgt]
          have h_delta : delta = true := by simp [delta, gate_parity_flip, hgt]
          rw [h_delta, Bool.xor_true] at h_inputs_mono
          match h_inputs : g.inputs with
          | [] => exact is_monotone_of_eq false p
          | [u] =>
            simp only [List.map_cons, List.map_nil]
            have h_mono_u : is_monotone
                (eval_node_fuel c (Function.update assignment i false) fuel u)
                (eval_node_fuel c (Function.update assignment i true) fuel u)
                (!p) := by
              have hlen : inputs0.length = 1 := by simp [inputs0, h_inputs]
              have := h_inputs_mono 0 (by omega)
              simp only [inputs0, inputs1, h_inputs, List.map_cons, List.map_nil] at this
              simp only [List.getElem!_cons_zero] at this
              exact this
            have := not_gate_monotone _ _ (!p) h_mono_u
            simp only [Bool.not_not] at this
            exact this
          | _ :: _ :: _ => exact is_monotone_of_eq false p

theorem value_monotone
    (c : Circuit)
    (h_valid : circuit_valid c)
    (h_mono_circuit : circuit_is_monotone c)
    (i : ℕ) (h_i_input : i < c.num_inputs)
    (v : ℕ) (p : Bool)
    (h_uniform : UniformParityTo c i v p) :
    ∀ assignment : ℕ → Bool,
      is_monotone
        (eval_node c (Function.update assignment i false) v)
        (eval_node c (Function.update assignment i true) v)
        p := by
  unfold eval_node
  exact value_monotone_fuel c h_valid.2 h_mono_circuit i h_i_input (total_nodes c) v p h_uniform

-- ============================================================================
-- Main Theorem: Pure Literal Rule for Circuits
-- ============================================================================

lemma uniform_parity_to_output_exists (c : Circuit) (i out : ℕ) (p : Bool)
    (h_uniform : UniformParity c i p) (_h_out : is_output c out)
    (h_reach : ParityReachesAny c i out) :
    UniformParityTo c i out p := ⟨h_reach, h_uniform.2 out _h_out⟩

/-- The optimal value to assign based on parity:
    - Even parity (false): assign true (positive polarity)
    - Odd parity (true): assign false (negative polarity) -/
def optimal_value (p : Bool) : Bool := if p then false else true

/-- Main theorem: If input i has uniform parity p to ALL outputs, then
    the circuit's satisfiability is preserved when fixing i to the optimal value. -/
theorem uniform_parity_pure_literal
    (c : Circuit)
    (h_valid : circuit_valid c)
    (h_mono_circuit : circuit_is_monotone c)
    (i : ℕ) (h_i_input : i < c.num_inputs)
    (p : Bool)
    (h_uniform : UniformParity c i p) :
    (∃ assignment, circuit_satisfied c assignment) ↔
    (∃ assignment, circuit_satisfied c
      (Function.update assignment i (optimal_value p))) := by
  constructor
  · intro ⟨assignment, h_sat⟩
    use assignment
    unfold circuit_satisfied at *
    intro out h_out_mem
    by_cases h_reach : ParityReachesAny c i out
    · have h_uniform_out := uniform_parity_to_output_exists c i out p h_uniform h_out_mem h_reach
      have h_mono := value_monotone c h_valid h_mono_circuit i h_i_input out p h_uniform_out assignment
      have h_orig := h_sat out h_out_mem
      unfold is_monotone at h_mono
      unfold optimal_value
      split_ifs at h_mono ⊢ with hp
      · cases hai : assignment i with
        | false =>
          rw [update_eq_self_of_eq assignment i false hai]; exact h_orig
        | true =>
          have heq : Function.update assignment i true = assignment :=
            update_eq_self_of_eq assignment i true hai
          rw [← heq] at h_orig
          exact h_mono h_orig
      · cases hai : assignment i with
        | false =>
          have heq : Function.update assignment i false = assignment :=
            update_eq_self_of_eq assignment i false hai
          rw [← heq] at h_orig
          exact h_mono h_orig
        | true =>
          rw [update_eq_self_of_eq assignment i true hai]; exact h_orig
    · have h_no_reach : ¬ReachesOrEq c i out := fun h_r =>
        h_reach (parity_reaches_any_of_reaches_or_eq c i out h_r)
      have h_indep := value_independent_of_unreachable c h_valid i h_i_input out h_no_reach
      have h_orig := h_sat out h_out_mem
      unfold optimal_value
      split_ifs with hp
      · cases hai : assignment i with
        | false =>
          rw [update_eq_self_of_eq assignment i false hai]; exact h_orig
        | true =>
          have heq : Function.update assignment i true = assignment :=
            update_eq_self_of_eq assignment i true hai
          rw [← h_indep assignment, heq]; exact h_orig
      · cases hai : assignment i with
        | false =>
          have heq : Function.update assignment i false = assignment :=
            update_eq_self_of_eq assignment i false hai
          rw [h_indep assignment, heq]; exact h_orig
        | true =>
          rw [update_eq_self_of_eq assignment i true hai]; exact h_orig
  · intro ⟨assignment, h_sat⟩
    exact ⟨Function.update assignment i (optimal_value p), h_sat⟩

-- ============================================================================
-- Corollaries
-- ============================================================================

theorem uniform_parity_sat_equiv
    (c : Circuit) (h_valid : circuit_valid c) (h_mono_circuit : circuit_is_monotone c)
    (i : ℕ) (h_i_input : i < c.num_inputs) (p : Bool) (h_uniform : UniformParity c i p) :
    (∃ assignment, circuit_satisfied c assignment) ↔
    (∃ assignment, circuit_satisfied c (Function.update assignment i (optimal_value p))) :=
  uniform_parity_pure_literal c h_valid h_mono_circuit i h_i_input p h_uniform

theorem unreachable_implies_any_parity_works
    (c : Circuit) (h_valid : circuit_valid c)
    (i : ℕ) (h_i_input : i < c.num_inputs) (h_unreach : ¬reaches_output c i) :
    ∀ val : Bool,
    (∃ assignment, circuit_satisfied c assignment) ↔
    (∃ assignment, circuit_satisfied c (Function.update assignment i val)) := by
  intro val
  constructor
  · intro ⟨a, h_sat⟩
    use a
    unfold circuit_satisfied at *
    intro out h_out
    have h_no_reach : ¬ReachesOrEq c i out := fun h_r => h_unreach ⟨out, h_out, h_r⟩
    have h_indep := value_independent_of_unreachable c h_valid i h_i_input out h_no_reach
    have h_orig := h_sat out h_out
    cases hv : val with
    | false =>
      cases hai : a i with
      | false =>
        rw [update_eq_self_of_eq a i false hai]; exact h_orig
      | true =>
        have heq : Function.update a i true = a :=
          update_eq_self_of_eq a i true hai
        rw [← h_indep a, heq]; exact h_orig
    | true =>
      cases hai : a i with
      | false =>
        have heq : Function.update a i false = a :=
          update_eq_self_of_eq a i false hai
        rw [h_indep a, heq]; exact h_orig
      | true =>
        rw [update_eq_self_of_eq a i true hai]; exact h_orig
  · intro ⟨a, h_sat⟩
    exact ⟨Function.update a i val, h_sat⟩

end CSP.L2S
