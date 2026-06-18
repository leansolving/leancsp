import CSP.L2S.Backends.PB.Bench.Generators
import CSP.L2S.Symmetry
import Mathlib.Tactic

/-!
# Parametric variable symmetry breaking for the mutilated chessboard

The `2k×2k` mutilated board (two opposite same-colour corners removed) is invariant under the main
**diagonal reflection** `(r,c) ↦ (c,r)`.  With the *regular* indexing of `gen_mutilated`
(horizontals `h(r,c)=r*(N-1)+c`, verticals `v(r,c)=N(N-1)+r*N+c`, `N=2k`), this reflection is the
closed-form involution `mutRefl` that swaps `h(r,c) ↔ v(c,r)`.

This file proves, **parametrically in `k`**, that `mutRefl` is an involutive in-range permutation
of the placement variables (`reflN_invol`, `reflN_lt`), that it is a `VariableSymmetry` of
`gen_mutilated k` (`refl_is_variable_symmetry`), and hence that `mutilated_sb k` is a sound
`variableSymmetryBreakingConstraint` (`mutilated_sb_is_variable_symmetry_breaking`), giving the
end-to-end bridge `mutilated_unsat_of_var`.
-/

namespace CSP.L2S.PB.MutilatedSB

open CSP.L2S Bench IntCSP

/-! ### The reflection as a closed-form involution (parametric in `N = 2k`) -/

/-- The diagonal reflection on placement indices, abstracted over the board side `N`. -/
def reflN (N x : ℕ) : ℕ :=
  if x < N * (N - 1) then N * (N - 1) + (x % (N - 1)) * N + (x / (N - 1))
  else ((x - N * (N - 1)) % N) * (N - 1) + ((x - N * (N - 1)) / N)

lemma mutRefl_eq (k x : ℕ) : mutRefl k x = reflN (2 * k) x := by
  simp only [mutRefl, reflN]

/-- **Involutivity** — `reflN N` is its own inverse on the placement range, for any `N ≥ 2`. -/
lemma reflN_invol (N : ℕ) (hN : 2 ≤ N) (x : ℕ) (hx : x < 2 * N * (N - 1)) :
    reflN N (reflN N x) = x := by
  unfold reflN
  have hNpos : 0 < N := by omega
  have hN1 : 0 < N - 1 := by omega
  have hPP : 2 * N * (N - 1) = N * (N - 1) + N * (N - 1) := by ring
  by_cases hxh : x < N * (N - 1)
  · rw [if_pos hxh]
    set m := x % (N - 1) with hm
    set q := x / (N - 1) with hq
    have hmlt : m < N - 1 := Nat.mod_lt _ hN1
    have hqlt : q < N := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hxh)
    have hxqm : q * (N - 1) + m = x := by rw [hm, hq, Nat.mul_comm]; exact Nat.div_add_mod x (N - 1)
    have hbig : ¬ (N * (N - 1) + m * N + q < N * (N - 1)) := by nlinarith
    rw [if_neg hbig]
    have hsub : N * (N - 1) + m * N + q - N * (N - 1) = q + m * N := by omega
    rw [hsub, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hNpos,
        Nat.mod_eq_of_lt hqlt, Nat.div_eq_of_lt hqlt, Nat.zero_add]
    exact hxqm
  · rw [if_neg hxh]
    set y := x - N * (N - 1) with hy
    have hylt : y < N * (N - 1) := by omega
    set r := y / N with hr
    set c := y % N with hc
    have hclt : c < N := Nat.mod_lt _ hNpos
    have hrlt : r < N - 1 := Nat.div_lt_of_lt_mul hylt
    have hyrc : r * N + c = y := by rw [hr, hc, Nat.mul_comm]; exact Nat.div_add_mod y N
    have hsmall : c * (N - 1) + r < N * (N - 1) := by nlinarith
    rw [if_pos hsmall]
    have hmod : (c * (N - 1) + r) % (N - 1) = r := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrlt]
    have hdiv : (c * (N - 1) + r) / (N - 1) = c := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN1, Nat.div_eq_of_lt hrlt, Nat.zero_add]
    rw [hmod, hdiv]
    omega

/-- **In range** — `reflN N` maps the placement range to itself. -/
lemma reflN_lt (N : ℕ) (hN : 2 ≤ N) (x : ℕ) (hx : x < 2 * N * (N - 1)) :
    reflN N x < 2 * N * (N - 1) := by
  unfold reflN
  have hN1 : 0 < N - 1 := by omega
  have hNpos : 0 < N := by omega
  by_cases hxh : x < N * (N - 1)
  · rw [if_pos hxh]
    have hmlt : x % (N - 1) < N - 1 := Nat.mod_lt _ hN1
    have hqlt : x / (N - 1) < N := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hxh)
    nlinarith
  · rw [if_neg hxh]
    set y := x - N * (N - 1) with hy
    have hPP : 2 * N * (N - 1) = N * (N - 1) + N * (N - 1) := by ring
    have hylt : y < N * (N - 1) := by omega
    have hclt : (y % N) < N := Nat.mod_lt _ hNpos
    have hrlt : y / N < N - 1 := Nat.div_lt_of_lt_mul hylt
    nlinarith

/-! ### The reflection as a permutation of the placement variables -/

/-- The reflection on placement variables of `gen_mutilated k`, as a permutation (`k ≥ 1`). -/
def reflPerm (k : ℕ) (hk : 1 ≤ k) : Equiv.Perm (Fin (2 * (2 * k) * (2 * k - 1))) :=
  Function.Involutive.toPerm
    (fun x => ⟨reflN (2 * k) x.val, reflN_lt (2 * k) (by omega) x.val x.isLt⟩)
    (fun x => Fin.ext (reflN_invol (2 * k) (by omega) x.val x.isLt))

@[simp] lemma reflPerm_val (k : ℕ) (hk : 1 ≤ k) (x : Fin (2 * (2 * k) * (2 * k - 1))) :
    (reflPerm k hk x).val = reflN (2 * k) x.val := rfl

/-! ### The removed-corner predicate is symmetric (parametric) -/

/-- The removed corners `(0,0)`, `(N-1,N-1)` lie on the diagonal, so the predicate is symmetric. -/
lemma mutRemoved_symm (N a b : ℕ) : mutRemoved N a b = mutRemoved N b a := by
  simp only [mutRemoved]; ac_rfl

/-! ### The reflection preserves dead/live placements (parametric) -/

/-- A placement and its reflection have the same dead/live status: the reflection swaps the two
    cells of a domino and `mutRemoved` is diagonal-symmetric. -/
lemma dead_refl (k : ℕ) (hk : 1 ≤ k) (x : ℕ) (hx : x < 2 * (2 * k) * (2 * k - 1)) :
    mutDead k (reflN (2 * k) x) = mutDead k x := by
  simp only [mutDead, reflN]
  set N := 2 * k with hNdef
  have hN : 2 ≤ N := by omega
  have hN1 : 0 < N - 1 := by omega
  have hNpos : 0 < N := by omega
  have hPP : 2 * N * (N - 1) = N * (N - 1) + N * (N - 1) := by ring
  by_cases hxh : x < N * (N - 1)
  · simp only [if_pos hxh]
    set m := x % (N - 1) with hm
    set q := x / (N - 1) with hq
    have hmlt : m < N - 1 := Nat.mod_lt _ hN1
    have hqlt : q < N := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hxh)
    have hge : ¬ (N * (N - 1) + m * N + q < N * (N - 1)) := by nlinarith
    rw [if_neg hge]
    have hsub : N * (N - 1) + m * N + q - N * (N - 1) = q + m * N := by omega
    rw [hsub, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ hNpos,
        Nat.mod_eq_of_lt hqlt, Nat.div_eq_of_lt hqlt, Nat.zero_add]
    rw [mutRemoved_symm N m q, mutRemoved_symm N (m + 1) q]
  · simp only [if_neg hxh]
    set y := x - N * (N - 1) with hy
    have hylt : y < N * (N - 1) := by omega
    set r := y / N with hr
    set c := y % N with hc
    have hclt : c < N := Nat.mod_lt _ hNpos
    have hrlt : r < N - 1 := Nat.div_lt_of_lt_mul hylt
    have hsmall : c * (N - 1) + r < N * (N - 1) := by nlinarith
    rw [if_pos hsmall]
    have hmod : (c * (N - 1) + r) % (N - 1) = r := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrlt]
    have hdiv : (c * (N - 1) + r) / (N - 1) = c := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN1, Nat.div_eq_of_lt hrlt, Nat.zero_add]
    rw [hmod, hdiv, mutRemoved_symm N c r, mutRemoved_symm N c (r + 1)]

/-! ### Per-element reflection of the two placement kinds -/

/-- A horizontal placement `h(r,c)` reflects to the vertical placement `v(c,r)`. -/
lemma reflN_h (N r c : ℕ) (_hN : 2 ≤ N) (hr : r < N) (hc : c < N - 1) :
    reflN N (r * (N - 1) + c) = N * (N - 1) + c * N + r := by
  unfold reflN
  have hN1 : 0 < N - 1 := by omega
  have hlt : r * (N - 1) + c < N * (N - 1) := by nlinarith
  rw [if_pos hlt, Nat.add_comm (r * (N - 1)) c, Nat.add_mul_mod_self_right,
      Nat.add_mul_div_right _ _ (by omega : 0 < N - 1), Nat.mod_eq_of_lt hc,
      Nat.div_eq_of_lt hc, Nat.zero_add]

/-- A vertical placement `v(r,c)` reflects to the horizontal placement `h(c,r)`. -/
lemma reflN_v (N r c : ℕ) (_hN : 2 ≤ N) (_hr : r < N - 1) (hc : c < N) :
    reflN N (N * (N - 1) + r * N + c) = c * (N - 1) + r := by
  unfold reflN
  have hge : ¬ (N * (N - 1) + r * N + c < N * (N - 1)) := by nlinarith
  rw [if_neg hge]
  have hsub : N * (N - 1) + r * N + c - N * (N - 1) = c + r * N := by omega
  rw [hsub, Nat.add_mul_mod_self_right, Nat.add_mul_div_right _ _ (by omega : 0 < N),
      Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc, Nat.zero_add]

/-! ### The reflection permutes a cell's incident dominoes to the reflected cell's -/

/-- The image under reflection of cell `(r,c)`'s incident placements is a permutation of cell
    `(c,r)`'s incident placements. -/
lemma incident_refl (k r c : ℕ) (hk : 1 ≤ k) (hr : r < 2 * k) (hc : c < 2 * k) :
    ((mutIncident k r c).map (reflN (2 * k))).Perm (mutIncident k c r) := by
  have hN : 2 ≤ 2 * k := by omega
  simp only [mutIncident, List.map_append]
  have eR : List.map (reflN (2*k)) (if c + 1 < 2*k then [r*(2*k-1)+c] else [])
          = (if c + 1 < 2*k then [2*k*(2*k-1) + c*(2*k) + r] else []) := by
    by_cases h : c + 1 < 2*k
    · rw [if_pos h, if_pos h]; simp only [List.map_cons, List.map_nil,
        reflN_h (2*k) r c hN hr (by omega)]
    · simp only [if_neg h, List.map_nil]
  have eL : List.map (reflN (2*k)) (if 0 < c then [r*(2*k-1)+(c-1)] else [])
          = (if 0 < c then [2*k*(2*k-1) + (c-1)*(2*k) + r] else []) := by
    by_cases h : 0 < c
    · rw [if_pos h, if_pos h]; simp only [List.map_cons, List.map_nil,
        reflN_h (2*k) r (c-1) hN hr (by omega)]
    · simp only [if_neg h, List.map_nil]
  have eD : List.map (reflN (2*k)) (if r + 1 < 2*k then [2*k*(2*k-1)+r*(2*k)+c] else [])
          = (if r + 1 < 2*k then [c*(2*k-1) + r] else []) := by
    by_cases h : r + 1 < 2*k
    · rw [if_pos h, if_pos h]; simp only [List.map_cons, List.map_nil,
        reflN_v (2*k) r c hN (by omega) hc]
    · simp only [if_neg h, List.map_nil]
  have eU : List.map (reflN (2*k)) (if 0 < r then [2*k*(2*k-1)+(r-1)*(2*k)+c] else [])
          = (if 0 < r then [c*(2*k-1) + (r-1)] else []) := by
    by_cases h : 0 < r
    · rw [if_pos h, if_pos h]; simp only [List.map_cons, List.map_nil,
        reflN_v (2*k) (r-1) c hN (by omega) hc]
    · simp only [if_neg h, List.map_nil]
  rw [eR, eL, eD, eU]
  -- LHS = D ++ U' ++ R ++ L'  ;  RHS = R ++ L' ++ D ++ U'  (same four blocks, rotated)
  set D := (if c + 1 < 2*k then [2*k*(2*k-1) + c*(2*k) + r] else []) with hD
  set U := (if 0 < c then [2*k*(2*k-1) + (c-1)*(2*k) + r] else []) with hU
  set R := (if r + 1 < 2*k then [c*(2*k-1) + r] else []) with hR
  set L := (if 0 < r then [c*(2*k-1) + (r-1)] else []) with hL
  rw [List.append_assoc (D ++ U) R L, List.append_assoc (R ++ L) D U]
  exact List.perm_append_comm

/-! ### Reading an assignment through the reflection -/

lemma valAt_refl (k : ℕ) (hk : 1 ≤ k) (a : IntAssignment (2 * (2 * k) * (2 * k - 1))) (x : ℕ)
    (hx : x < 2 * (2 * k) * (2 * k - 1)) :
    valAt (a ∘ reflPerm k hk) x = valAt a (reflN (2 * k) x) := by
  have hrx : reflN (2 * k) x < 2 * (2 * k) * (2 * k - 1) := reflN_lt (2 * k) (by omega) x hx
  simp only [valAt, hx, hrx, dif_pos, Function.comp_apply]
  exact congrArg a (Fin.ext (reflPerm_val k hk ⟨x, hx⟩))

/-- Every incident placement index is in range. -/
lemma incident_lt (k r c : ℕ) (hk : 1 ≤ k) (hr : r < 2 * k) (hc : c < 2 * k) :
    ∀ v ∈ mutIncident k r c, v < 2 * (2 * k) * (2 * k - 1) := by
  intro v hv
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 2 := ⟨2 * k - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  simp only [mutIncident, hm, e1, List.mem_append, List.mem_ite_nil_right,
    List.mem_singleton] at hv hr hc ⊢
  rcases hv with ((h | h) | h) | h
  · rw [h.2]; nlinarith [hr, hc]
  · have hc0 : 0 < c := h.1; rw [h.2]
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith [hr, hc]
  · rw [h.2]; nlinarith [hr, hc, h.1]
  · have hr0 : 0 < r := h.1; rw [h.2]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp only [Nat.add_sub_cancel]; nlinarith [hr, hc]

/-! ### The reflection is a variable symmetry of `gen_mutilated` -/

theorem refl_is_variable_symmetry (k : ℕ) (hk : 1 ≤ k) :
    VariableSymmetry (gen_mutilated k) (reflPerm k hk) := by
  intro a hsol c hc
  have hc2 : c ∈ (List.range (2 * (2 * k) * (2 * k - 1))).map
        (fun x => IntConstraint.bound x 0 (if mutDead k x then 0 else 1))
      ++ (List.range (2 * k)).flatMap (fun r => (List.range (2 * k)).filterMap
        (fun c => if mutRemoved (2 * k) r c then none
                  else some (IntConstraint.exactly_k (mutIncident k r c) 1))) := hc
  rcases List.mem_append.mp hc2 with hb | hcell
  · -- bound x 0 (dead? 0 : 1)
    obtain ⟨x, hxr, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hxr
    have hrx : reflN (2 * k) x < 2 * (2 * k) * (2 * k - 1) := reflN_lt (2 * k) (by omega) x hxr
    have hmem : IntConstraint.bound (reflN (2 * k) x) 0 (if mutDead k (reflN (2 * k) x) then 0 else 1)
        ∈ (gen_mutilated k).constraints :=
      List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨reflN (2 * k) x, List.mem_range.mpr hrx, rfl⟩))
    have hb' := hsol _ hmem
    show satisfiesConstraintInt (IntConstraint.bound x 0 (if mutDead k x then 0 else 1))
      (a ∘ reflPerm k hk)
    simp only [satisfiesConstraintInt, patternHolds] at hb' ⊢
    rw [show valAt (a ∘ reflPerm k hk) x = valAt a (reflN (2 * k) x) from valAt_refl k hk a x hxr]
    rw [dead_refl k hk x hxr] at hb'
    exact hb'
  · -- exactly_k (mutIncident k r c') 1
    obtain ⟨r, hrr, hrest⟩ := List.mem_flatMap.mp hcell
    obtain ⟨c', hc'r, hfm⟩ := List.mem_filterMap.mp hrest
    rw [List.mem_range] at hrr hc'r
    by_cases hh : mutRemoved (2 * k) r c' = true
    · rw [if_pos hh] at hfm; exact absurd hfm (by simp)
    · rw [if_neg hh, Option.some_inj] at hfm
      rw [← hfm]
      have hh' : mutRemoved (2 * k) c' r = false := by rw [mutRemoved_symm]; simpa using hh
      have hmem : IntConstraint.exactly_k (mutIncident k c' r) 1 ∈ (gen_mutilated k).constraints :=
        List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨c', List.mem_range.mpr hc'r,
          List.mem_filterMap.mpr ⟨r, List.mem_range.mpr hrr, by rw [hh']; rfl⟩⟩))
      have he := hsol _ hmem
      simp only [satisfiesConstraintInt, patternHolds] at he ⊢
      show (List.map (valAt (a ∘ reflPerm k hk)) (mutIncident k r c')).sum = ((1 : ℕ) : ℤ)
      have hmap : (mutIncident k r c').map (valAt (a ∘ reflPerm k hk))
                = ((mutIncident k r c').map (reflN (2 * k))).map (valAt a) := by
        rw [List.map_map]
        exact List.map_congr_left fun v hv =>
          valAt_refl k hk a v (incident_lt k r c' hk hrr hc'r v hv)
      rw [hmap, (incident_refl k r c' hk hrr hc'r |>.map (valAt a)).sum_eq]
      exact he

/-! ### The symmetry-breaking constraint is sound -/

theorem mutilated_sb_is_variable_symmetry_breaking (k : ℕ) (hk : 1 ≤ k) :
    variableSymmetryBreakingConstraint (gen_mutilated k) (mutilated_sb k) := by
  have h1 : (1 : ℕ) < 2 * (2 * k) * (2 * k - 1) := by
    have : 2 ≤ 2 * k := by omega
    have : 1 ≤ 2 * k - 1 := by omega
    nlinarith
  have hr1 : reflN (2 * k) 1 < 2 * (2 * k) * (2 * k - 1) := reflN_lt (2 * k) (by omega) 1 h1
  intro a hsol
  by_cases hle : valAt a 1 ≤ valAt a (reflN (2 * k) 1)
  · -- a already satisfies the lex break: use the identity symmetry
    refine ⟨Equiv.refl _, VariableSymmetry.identity_is_symmetry _, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · show satisfiesConstraintInt (mutilated_sb k) (a ∘ Equiv.refl _)
      simp only [mutilated_sb, satisfiesConstraintInt, patternHolds, mutRefl_eq,
        Equiv.coe_refl]
      exact hle
    · exact hsol c hmem
  · -- otherwise the reflection swaps the two values and satisfies the break
    refine ⟨reflPerm k hk, refl_is_variable_symmetry k hk, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · show satisfiesConstraintInt (mutilated_sb k) (a ∘ reflPerm k hk)
      simp only [mutilated_sb, satisfiesConstraintInt, patternHolds, mutRefl_eq]
      rw [show valAt (a ∘ reflPerm k hk) 1 = valAt a (reflN (2 * k) 1) from valAt_refl k hk a 1 h1,
          show valAt (a ∘ reflPerm k hk) (reflN (2 * k) 1)
              = valAt a (reflN (2 * k) (reflN (2 * k) 1)) from valAt_refl k hk a (reflN (2 * k) 1) hr1,
          reflN_invol (2 * k) (by omega) 1 h1]
      omega
    · exact refl_is_variable_symmetry k hk a hsol c hmem

theorem mutilated_unsat_of_var (k : ℕ) (hk : 1 ≤ k)
    (h_unsat : ¬ isSatisfiableInt ((gen_mutilated k).addConstraint (mutilated_sb k))) :
    ¬ isSatisfiableInt (gen_mutilated k) :=
  unsat_of_variable_sbc (gen_mutilated k) (mutilated_sb k)
    (mutilated_sb_is_variable_symmetry_breaking k hk) h_unsat

end CSP.L2S.PB.MutilatedSB
