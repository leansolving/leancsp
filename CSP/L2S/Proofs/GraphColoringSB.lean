import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Translate
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.List.FinRange

open CSP.L2S

/-!
## Graph Coloring Problem

Variables: One per node
Domains: Colors (integers 0..k-1)
Constraints: Adjacent nodes have different colors (ne constraints)
-/

-- ============================================================================
-- CSP Definition
-- ============================================================================

/- Bound constraints -/
def bound_constraints (nodes : ℕ) (colors : ℕ) : List (TaggedConstraint nodes) :=
  (List.finRange nodes).map (fun v => bound v 0 (colors-1))

/- Problem constraints: adjacent edges have different colors -/
def edge_constraints (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) : List (TaggedConstraint nodes) :=
  edges.map (fun (u,v) => not_equal u v)

/- CSP: bound + edges constraints -/
def graph_coloring_csp (nodes : ℕ) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : HomogeneousCSP :=
  ⟨ nodes ,
    bound_constraints nodes colors ++ edge_constraints nodes edges ⟩


-- ============================================================================
-- Symmetry Breaking Constraint Definition
-- ============================================================================

/- Our candidate to symmetry breaking constraint (fix the color of node 0 to 0)-/
def sb_constraint (nodes : ℕ) (h_nodes : 0 < nodes) : TaggedConstraint nodes :=
  equals_const ⟨0, h_nodes⟩ 0

/- Extended CSP (including the SBC) -/
def extended_graph_coloring_csp (nodes : ℕ) (h_nodes : 0 < nodes) (edges : List (Fin nodes × Fin nodes)) (colors : ℕ) : HomogeneousCSP :=
  (graph_coloring_csp nodes edges colors).addConstraint (sb_constraint nodes h_nodes)


-- ============================================================================
-- Symmetry Function
-- ============================================================================

/-- Color swap: swaps color 0 with color c, leaves others unchanged -/
def color_swap (c : ℤ) : Equiv.Perm HomogeneousDomain :=
  Equiv.swap 0 c

-- ============================================================================
-- Auxiliary Lemmas
-- ============================================================================

/-- Color swaps preserve the interval [0, colors-1] when c is in that interval -/
lemma intervalPreserving_color_swap (colors : ℕ) (c : ℤ)
    (h_colors : 0 < colors)
    (h_c : 0 ≤ c ∧ c < colors) :
    intervalPreserving (color_swap c) 0 (colors - 1) := by
  intro d
  unfold color_swap
  constructor
  · intro ⟨h_lb, h_ub⟩
    by_cases h1 : d = 0
    · simp [h1, Equiv.swap_apply_left]
      exact ⟨h_c.1, by omega⟩
    · by_cases h2 : d = c
      · simp [h2, Equiv.swap_apply_right]
        omega
      · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact ⟨h_lb, h_ub⟩
  · intro ⟨h_lb, h_ub⟩
    by_cases h1 : d = 0
    · omega
    · by_cases h2 : d = c
      · rw [h2]
        exact ⟨h_c.1, by omega⟩
      · simp [Equiv.swap_apply_of_ne_of_ne h1 h2] at h_lb h_ub
        exact ⟨h_lb, h_ub⟩

/-- Not-equal constraints are preserved by any permutation (due to injectivity) -/
lemma not_equal_preserved_by_swap {num_vars : ℕ}
    (δ : Equiv.Perm HomogeneousDomain)
    (u v : HomogeneousVarIndex num_vars) :
    taggedConstraintDomainSymmetric (not_equal u v) δ := by
  unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
  intro assignment h_sat
  unfold not_equal CSP.satisfies_dynamic_constraint at *
  simp only [CSP.binary_dynamic_constraint] at *
  unfold CSP.satisfies_constraint CSP.sat at *
  unfold CSP.binary_constraint CSP.map_assignment at *
  simp only [_root_.Vector.get] at *
  simp only [decide_eq_true_iff] at *
  intro h_eq
  apply h_sat
  exact δ.injective h_eq

-- ============================================================================
-- Symmetry-Breaking Correctness
-- ============================================================================

/-- Result 1: Color swap is a domain symmetry for graph coloring -/
theorem color_swap_is_symmetry (nodes colors : ℕ)
    (edges : List (Fin nodes × Fin nodes)) (c : ℤ)
    (h_colors : 0 < colors)
    (h_c : 0 ≤ c ∧ c < colors) :
    DomainSymmetry (graph_coloring_csp nodes edges colors) (color_swap c) := by
  apply domain_symmetry_preserves_solutions
  intro tc h_tc_mem
  unfold graph_coloring_csp at h_tc_mem
  simp only [List.mem_append] at h_tc_mem
  obtain h_bound | h_edge := h_tc_mem
  · unfold bound_constraints at h_bound
    simp only [List.mem_map] at h_bound
    obtain ⟨v, _, h_eq⟩ := h_bound
    rw [← h_eq]
    unfold taggedConstraintDomainSymmetric constraintDomainSymmetric
    intro assignment h_sat
    have h_interval := intervalPreserving_color_swap colors c h_colors h_c
    have h_preserves := intervalPreserving_preserves_bound (color_swap c) v 0 (colors - 1) h_interval assignment
    exact h_preserves.mp h_sat
  · unfold edge_constraints at h_edge
    simp only [List.mem_map] at h_edge
    obtain ⟨⟨u, v⟩, _, h_eq⟩ := h_edge
    rw [← h_eq]
    exact not_equal_preserved_by_swap (color_swap c) u v

/-- Result 2: The symmetry breaking constraint is a domain symmetry breaking constraint -/
theorem sb_constraint_is_domain_symmetry_breaking (nodes colors : ℕ)
    (h_nodes : 0 < nodes) (h_colors : 0 < colors)
    (edges : List (Fin nodes × Fin nodes)) :
    domainSymmetryBreakingConstraint
      (graph_coloring_csp nodes edges colors)
      (sb_constraint nodes h_nodes) := by
  intro assignment h_sol
  by_cases h : assignment ⟨0, h_nodes⟩ = 0
  · use DomainSymmetry.identity
    constructor
    · exact DomainSymmetry.identity_is_symmetry _
    · intro tc h_tc_mem
      simp only [HomogeneousCSP.addConstraint, List.mem_cons] at h_tc_mem
      obtain h_sbc | h_orig := h_tc_mem
      · rw [h_sbc]
        unfold HomogeneousCSP.satisfiesConstraint sb_constraint equals_const
        unfold CSP.satisfies_dynamic_constraint CSP.unary_dynamic_constraint
        unfold CSP.satisfies_constraint CSP.sat CSP.unary_constraint CSP.map_assignment
        simp only [_root_.Vector.get, decide_eq_true_iff, Function.comp_apply]
        simp only [DomainSymmetry.identity, Equiv.refl_apply]
        exact h
      · unfold HomogeneousCSP.isSolution at h_sol
        simp only [DomainSymmetry.identity]
        exact h_sol tc h_orig
  · let c := assignment ⟨0, h_nodes⟩
    have h_c_in_bounds : 0 ≤ c ∧ c < colors := by
      have h_bound : bound ⟨0, h_nodes⟩ 0 (colors - 1) ∈ (graph_coloring_csp nodes edges colors).constraints := by
        unfold graph_coloring_csp bound_constraints
        simp only [List.mem_append, List.mem_map, List.mem_finRange]
        left
        use ⟨0, h_nodes⟩
      unfold HomogeneousCSP.isSolution HomogeneousCSP.satisfiesConstraint at h_sol
      have h_sat_bound := h_sol (bound ⟨0, h_nodes⟩ 0 (colors - 1)) h_bound
      unfold bound CSP.satisfies_dynamic_constraint at h_sat_bound
      simp only [CSP.satisfies_constraint, CSP.sat, CSP.map_assignment, extractValues, _root_.Vector.get, List.ofFn] at h_sat_bound
      have : decide (0 ≤ c ∧ c ≤ ↑colors - 1) = true := h_sat_bound
      simp only [decide_eq_true_iff] at this
      constructor
      · exact this.1
      · have this_r : c ≤ ↑colors - 1 := this.2
        exact Int.lt_of_le_sub_one this_r
    use color_swap c
    constructor
    · exact color_swap_is_symmetry nodes colors edges c h_colors h_c_in_bounds
    · intro tc h_tc_mem
      simp only [HomogeneousCSP.addConstraint, List.mem_cons] at h_tc_mem
      obtain h_sbc | h_orig := h_tc_mem
      · rw [h_sbc]
        unfold HomogeneousCSP.satisfiesConstraint sb_constraint equals_const
        unfold CSP.satisfies_dynamic_constraint CSP.unary_dynamic_constraint
        unfold CSP.satisfies_constraint CSP.sat CSP.unary_constraint CSP.map_assignment
        simp only [_root_.Vector.get, decide_eq_true_iff, Function.comp_apply]
        show (color_swap c) (assignment ⟨0, h_nodes⟩) = 0
        unfold color_swap
        rw [Equiv.swap_apply_right]
      · have h_sym := color_swap_is_symmetry nodes colors edges c h_colors h_c_in_bounds
        unfold DomainSymmetry at h_sym
        have h_sol_orig := h_sym assignment h_sol
        exact h_sol_orig tc h_orig

/-- Result 3: The symmetry breaking constraint is a general symmetry breaking constraint -/
theorem sb_constraint_is_symmetry_breaking (nodes colors : ℕ)
    (h_nodes : 0 < nodes) (h_colors : 0 < colors)
    (edges : List (Fin nodes × Fin nodes)) :
    symmetryBreakingConstraint
      (graph_coloring_csp nodes edges colors)
      (sb_constraint nodes h_nodes) := by
  left  -- Choose domain symmetry breaking
  exact sb_constraint_is_domain_symmetry_breaking nodes colors h_nodes h_colors edges

/-- Result 4: Equisatisfiability - The extended CSP is equisatisfiable with the original -/
theorem graph_coloring_equisatisfiability (nodes colors : ℕ)
    (h_nodes : 0 < nodes) (h_colors : 0 < colors)
    (edges : List (Fin nodes × Fin nodes)) :
    equisatisfiable
      (graph_coloring_csp nodes edges colors)
      (extended_graph_coloring_csp nodes h_nodes edges colors) := by
  apply domainSymmetryBreaking_equisatisfiability
  exact sb_constraint_is_domain_symmetry_breaking nodes colors h_nodes h_colors edges

-- ============================================================================
-- Solver conversion
-- ============================================================================

/-- Generate a k-colorable graph by partitioning n nodes into k independent sets
    and adding random edges only between different sets.

    Parameters:
    - n: number of nodes
    - k: number of colors (and independent sets)
    - p_num, p_den: edge probability p = p_num/p_den for inter-set edges
    - seed: random seed for reproducibility

    Returns: List of edges (guaranteed k-colorable)

    Algorithm:
    - Node i belongs to independent set (i % k)
    - Edges are only added between nodes in DIFFERENT independent sets
    - This guarantees k-colorability: assign color (i % k) to each node
-/
def kColorableGraphEdges (n k : ℕ) (p_num p_den : ℕ) (seed : ℕ) : List (Fin n × Fin n) :=
  if k = 0 then [] else
  let m := 2147483648  -- 2^31
  let a := 1103515245
  let c := 12345
  -- Generate edges only between nodes in DIFFERENT independent sets
  let (edges, _) := (List.finRange n).foldl (fun (acc_edges, s) i =>
    (List.finRange n).foldl (fun (acc_edges2, s2) j =>
      if i.val < j.val then
        -- Only consider edge if nodes are in DIFFERENT independent sets
        if i.val % k ≠ j.val % k then
          let s_new := (a * s2 + c) % m
          let random_val := s_new % p_den
          if random_val < p_num then
            ((i, j) :: acc_edges2, s_new)
          else
            (acc_edges2, s_new)
        else
          -- Same independent set: never add edge (preserves independent set property)
          (acc_edges2, s2)
      else
        (acc_edges2, s2)
    ) (acc_edges, s)
  ) ([], seed)
  edges.reverse


-- Helper: Compute k (number of colors) based on n, scaling with problem size
def computeK (n : ℕ) : ℕ := max 3 (n / 10)

def main : IO Unit := do
  let sizes := [10,20,30,40,50,60,70,80,90,100]
  let seed := 42

  -- K-COLORABLE INSTANCES (guaranteed satisfiable)
  IO.println "\nGenerating k-Colorable Graph instances (guaranteed satisfiable)..."

  for n in sizes do
    if h_n : 0 < n then
      let k := computeK n
      let edges := kColorableGraphEdges n k 8 10 (seed + n)  -- p = 0.8

      IO.println s!"Generating k-colorable G({n}, k={k}, p=0.8)..."

      let base_csp := graph_coloring_csp n edges k
      let sbc_csp := extended_graph_coloring_csp n h_n edges k

      -- Generate to new kcolorable/ directory
      saveToAuto base_csp s!"CSP/L2S/Proofs/mzn/graphcoloring/kcolorable/base_{n}" BackendType.MiniZinc
      saveToAuto base_csp s!"CSP/L2S/Proofs/smt2/graphcoloring/kcolorable/base_{n}" BackendType.SMTLIB
      saveToAuto sbc_csp s!"CSP/L2S/Proofs/mzn/graphcoloring/kcolorable/sbc_{n}" BackendType.MiniZinc
      saveToAuto sbc_csp s!"CSP/L2S/Proofs/smt2/graphcoloring/kcolorable/sbc_{n}" BackendType.SMTLIB
