import CSP.L2S.Backends.PB.Bench.Generators
import CSP.L2S.Symmetry
import Mathlib.Tactic

/-!
# Parametric variable symmetry breaking for the perfect-matching / parity principle

`gen_matching m` encodes a perfect matching on `Kₙ` (`n = 2m+1`) over the `n×n` adjacency:
variable `x_{ij} = i*n+j ∈ {0,1}` (diagonal forced 0), symmetric (`x_{ij} = x_{ji}`), each row
summing to 1.  The vertex transposition `(0 1)` acts on indices by `matchSwap` — the closed-form
involution `i*n+j ↦ σi*n+σj` with `σ` swapping `0,1`.

This file proves, **parametrically in `m`**, that `matchSwap` is an involutive in-range permutation
of the variables, that it is a `VariableSymmetry` of `gen_matching m`, and hence that
`matching_sb m` is a sound `variableSymmetryBreakingConstraint`, giving `matching_unsat_of_var`.
-/

namespace CSP.L2S.PB.MatchingSB

open CSP.L2S Bench IntCSP

/-! ### The coordinate transposition `(0 1)` -/

/-- Swap `0 ↔ 1`, fixing everything else. -/
def swap01 (a : ℕ) : ℕ := if a = 0 then 1 else if a = 1 then 0 else a

lemma swap01_invol (a : ℕ) : swap01 (swap01 a) = a := by
  rcases a with _ | _ | a <;> simp [swap01]

lemma swap01_lt (n a : ℕ) (hn : 2 ≤ n) (ha : a < n) : swap01 a < n := by
  rcases a with _ | _ | a <;> simp only [swap01] <;> split_ifs <;> omega

lemma swap01_inj {a b : ℕ} : swap01 a = swap01 b ↔ a = b := by
  rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp [swap01]

lemma swap01_beq (a b : ℕ) : (swap01 a == swap01 b) = (a == b) := by
  rcases eq_or_ne a b with h | h
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr (by rw [ne_eq, swap01_inj]; exact h),
        beq_eq_false_iff_ne.mpr h]

/-! ### The transposition on adjacency indices (parametric in `m`, `n = 2m+1`) -/

/-- `matchSwap m (i*n+j) = swap01 i * n + swap01 j` for in-range `i,j`. -/
lemma matchSwap_pair (m i j : ℕ) (hj : j < 2 * m + 1) :
    matchSwap m (i * (2 * m + 1) + j) = swap01 i * (2 * m + 1) + swap01 j := by
  have hd : (i * (2 * m + 1) + j) / (2 * m + 1) = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (i * (2 * m + 1) + j) % (2 * m + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  simp only [matchSwap, hd, hmod, swap01]

/-- **In range** — `matchSwap` maps the variable range to itself. -/
lemma matchSwap_lt (m x : ℕ) (hm : 1 ≤ m) (hx : x < (2 * m + 1) * (2 * m + 1)) :
    matchSwap m x < (2 * m + 1) * (2 * m + 1) := by
  have hn : 2 ≤ 2 * m + 1 := by omega
  have hxd : x / (2 * m + 1) < 2 * m + 1 :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  have hxm : x % (2 * m + 1) < 2 * m + 1 := Nat.mod_lt _ (by omega)
  have ha : swap01 (x / (2 * m + 1)) < 2 * m + 1 := swap01_lt _ _ hn hxd
  have hb : swap01 (x % (2 * m + 1)) < 2 * m + 1 := swap01_lt _ _ hn hxm
  have hms : matchSwap m x = swap01 (x / (2 * m + 1)) * (2 * m + 1) + swap01 (x % (2 * m + 1)) := rfl
  rw [hms]; nlinarith [ha, hb]

/-- **Involutivity** — `matchSwap` is its own inverse on the variable range. -/
lemma matchSwap_invol (m x : ℕ) (hm : 1 ≤ m) (hx : x < (2 * m + 1) * (2 * m + 1)) :
    matchSwap m (matchSwap m x) = x := by
  have hn : 2 ≤ 2 * m + 1 := by omega
  have hxd : x / (2 * m + 1) < 2 * m + 1 :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx)
  have hxm : x % (2 * m + 1) < 2 * m + 1 := Nat.mod_lt _ (by omega)
  have hb : swap01 (x % (2 * m + 1)) < 2 * m + 1 := swap01_lt _ _ hn hxm
  have hms : matchSwap m x = swap01 (x / (2 * m + 1)) * (2 * m + 1) + swap01 (x % (2 * m + 1)) := rfl
  rw [hms, matchSwap_pair m _ _ hb, swap01_invol, swap01_invol, Nat.mul_comm, Nat.div_add_mod]

/-! ### As a permutation of the matching variables -/

/-- The transposition `(0 1)` as a permutation of the variables of `gen_matching m` (`m ≥ 1`). -/
def matchPerm (m : ℕ) (hm : 1 ≤ m) : Equiv.Perm (Fin ((2 * m + 1) * (2 * m + 1))) :=
  Function.Involutive.toPerm
    (fun x => ⟨matchSwap m x.val, matchSwap_lt m x.val hm x.isLt⟩)
    (fun x => Fin.ext (matchSwap_invol m x.val hm x.isLt))

@[simp] lemma matchPerm_val (m : ℕ) (hm : 1 ≤ m) (x : Fin ((2 * m + 1) * (2 * m + 1))) :
    (matchPerm m hm x).val = matchSwap m x.val := rfl

/-- Reading `a ∘ matchPerm` is reading `a` at the swapped index. -/
lemma valAt_swap (m : ℕ) (hm : 1 ≤ m) (a : IntAssignment ((2 * m + 1) * (2 * m + 1))) (x : ℕ)
    (hx : x < (2 * m + 1) * (2 * m + 1)) :
    valAt (a ∘ matchPerm m hm) x = valAt a (matchSwap m x) := by
  have hsx : matchSwap m x < (2 * m + 1) * (2 * m + 1) := matchSwap_lt m x hm hx
  simp only [valAt, hx, hsx, dif_pos, Function.comp_apply]
  exact congrArg a (Fin.ext (matchPerm_val m hm ⟨x, hx⟩))

/-! ### Structural facts used in the symmetry proof -/

/-- `matchSwap` of a decoded index, with its div/mod. -/
lemma matchSwap_divmod (m x : ℕ) (hm : 1 ≤ m) (_hx : x < (2 * m + 1) * (2 * m + 1)) :
    (matchSwap m x) / (2 * m + 1) = swap01 (x / (2 * m + 1)) ∧
    (matchSwap m x) % (2 * m + 1) = swap01 (x % (2 * m + 1)) := by
  have hn : 2 ≤ 2 * m + 1 := by omega
  have hxm : x % (2 * m + 1) < 2 * m + 1 := Nat.mod_lt _ (by omega)
  have hb : swap01 (x % (2 * m + 1)) < 2 * m + 1 := swap01_lt _ _ hn hxm
  have hms : matchSwap m x = swap01 (x / (2 * m + 1)) * (2 * m + 1) + swap01 (x % (2 * m + 1)) := rfl
  refine ⟨?_, ?_⟩
  · rw [hms, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega : 0 < 2 * m + 1),
        Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [hms, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- The diagonal predicate (`x/n == x%n`, the "is a diagonal cell" test) is swap-invariant. -/
lemma diag_swap (m x : ℕ) (hm : 1 ≤ m) (hx : x < (2 * m + 1) * (2 * m + 1)) :
    (if (matchSwap m x) / (2 * m + 1) == (matchSwap m x) % (2 * m + 1) then (0 : ℤ) else 1)
  = (if x / (2 * m + 1) == x % (2 * m + 1) then (0 : ℤ) else 1) := by
  obtain ⟨hd, hmo⟩ := matchSwap_divmod m x hm hx
  rw [hd, hmo, swap01_beq]

/-- `swap01` permutes `range n` (it just swaps the first two elements). -/
lemma map_swap01_range_perm (n : ℕ) (hn : 2 ≤ n) :
    ((List.range n).map swap01).Perm (List.range n) := by
  rw [List.perm_ext_iff_of_nodup
        (List.nodup_range.map fun a b => swap01_inj.mp) List.nodup_range]
  intro a
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact swap01_lt n b hn hb
  · intro ha; exact ⟨swap01 a, swap01_lt n a hn ha, swap01_invol a⟩

/-- The swap maps row `i` to a permutation of row `swap01 i`. -/
lemma row_swap (m i : ℕ) (hm : 1 ≤ m) :
    ((((List.range (2 * m + 1)).map (fun j => i * (2 * m + 1) + j)).map (matchSwap m))).Perm
    ((List.range (2 * m + 1)).map (fun j => swap01 i * (2 * m + 1) + j)) := by
  rw [List.map_map]
  have hmapeq : ((List.range (2 * m + 1)).map ((matchSwap m) ∘ (fun j => i * (2 * m + 1) + j)))
      = ((List.range (2 * m + 1)).map swap01).map (fun j => swap01 i * (2 * m + 1) + j) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    simp only [Function.comp_apply]
    rw [matchSwap_pair m i j hj]
  rw [hmapeq]
  exact (map_swap01_range_perm (2 * m + 1) (by omega)).map _

/-! ### The transposition is a variable symmetry of `gen_matching` -/

theorem match_is_variable_symmetry (m : ℕ) (hm : 1 ≤ m) :
    VariableSymmetry (gen_matching m) (matchPerm m hm) := by
  intro a hsol c hc
  have hc2 : c ∈ ((List.range ((2 * m + 1) * (2 * m + 1))).map
        (fun x => IntConstraint.bound x 0 (if x / (2 * m + 1) == x % (2 * m + 1) then 0 else 1))
      ++ (List.range (2 * m + 1)).flatMap (fun i => (List.range (2 * m + 1)).filterMap
          (fun j => if i < j then some (IntConstraint.eq (i * (2 * m + 1) + j) (j * (2 * m + 1) + i))
                    else none)))
      ++ (List.range (2 * m + 1)).map (fun i =>
          IntConstraint.exactly_k ((List.range (2 * m + 1)).map (fun j => i * (2 * m + 1) + j)) 1) :=
    hc
  rcases List.mem_append.mp hc2 with hbs | hrow
  rcases List.mem_append.mp hbs with hb | hsym
  · -- bound x 0 (diag? 0 : 1)
    obtain ⟨x, hxr, rfl⟩ := List.mem_map.mp hb
    rw [List.mem_range] at hxr
    have hsx : matchSwap m x < (2 * m + 1) * (2 * m + 1) := matchSwap_lt m x hm hxr
    have hmem : IntConstraint.bound (matchSwap m x) 0
        (if (matchSwap m x) / (2 * m + 1) == (matchSwap m x) % (2 * m + 1) then 0 else 1)
        ∈ (gen_matching m).constraints :=
      List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨matchSwap m x, List.mem_range.mpr hsx, rfl⟩))))
    have hb' := hsol _ hmem
    show satisfiesConstraintInt
      (IntConstraint.bound x 0 (if x / (2 * m + 1) == x % (2 * m + 1) then 0 else 1))
      (a ∘ matchPerm m hm)
    simp only [satisfiesConstraintInt, patternHolds] at hb' ⊢
    rw [show valAt (a ∘ matchPerm m hm) x = valAt a (matchSwap m x) from valAt_swap m hm a x hxr]
    rw [diag_swap m x hm hxr] at hb'
    exact hb'
  · -- symmetry constraint eq (i*n+j) (j*n+i),  i < j
    obtain ⟨i, hir, hrest⟩ := List.mem_flatMap.mp hsym
    obtain ⟨j, hjr, hfm⟩ := List.mem_filterMap.mp hrest
    rw [List.mem_range] at hir hjr
    by_cases hij : i < j
    · rw [if_pos hij, Option.some_inj] at hfm
      rw [← hfm]
      have hin : i * (2 * m + 1) + j < (2 * m + 1) * (2 * m + 1) := by nlinarith [hir, hjr]
      have hjn : j * (2 * m + 1) + i < (2 * m + 1) * (2 * m + 1) := by nlinarith [hir, hjr]
      have hsi : swap01 i < 2 * m + 1 := swap01_lt _ _ (by omega) hir
      have hsj : swap01 j < 2 * m + 1 := swap01_lt _ _ (by omega) hjr
      show satisfiesConstraintInt
        (IntConstraint.eq (i * (2 * m + 1) + j) (j * (2 * m + 1) + i)) (a ∘ matchPerm m hm)
      simp only [satisfiesConstraintInt, patternHolds]
      rw [show valAt (a ∘ matchPerm m hm) (i * (2 * m + 1) + j)
            = valAt a (matchSwap m (i * (2 * m + 1) + j)) from valAt_swap m hm a _ hin,
          show valAt (a ∘ matchPerm m hm) (j * (2 * m + 1) + i)
            = valAt a (matchSwap m (j * (2 * m + 1) + i)) from valAt_swap m hm a _ hjn,
          matchSwap_pair m i j hjr, matchSwap_pair m j i hir]
      rcases lt_trichotomy (swap01 i) (swap01 j) with hlt | heq | hgt
      · have hmem : IntConstraint.eq (swap01 i * (2 * m + 1) + swap01 j)
            (swap01 j * (2 * m + 1) + swap01 i) ∈ (gen_matching m).constraints :=
          List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
            (List.mem_flatMap.mpr ⟨swap01 i, List.mem_range.mpr hsi,
              List.mem_filterMap.mpr ⟨swap01 j, List.mem_range.mpr hsj, if_pos hlt⟩⟩))))
        have := hsol _ hmem
        simpa [satisfiesConstraintInt, patternHolds] using this
      · exact absurd (swap01_inj.mp heq) (by omega)
      · have hmem : IntConstraint.eq (swap01 j * (2 * m + 1) + swap01 i)
            (swap01 i * (2 * m + 1) + swap01 j) ∈ (gen_matching m).constraints :=
          List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
            (List.mem_flatMap.mpr ⟨swap01 j, List.mem_range.mpr hsj,
              List.mem_filterMap.mpr ⟨swap01 i, List.mem_range.mpr hsi, if_pos hgt⟩⟩))))
        have := hsol _ hmem
        have h2 : valAt a (swap01 j * (2 * m + 1) + swap01 i)
                = valAt a (swap01 i * (2 * m + 1) + swap01 j) := by
          simpa [satisfiesConstraintInt, patternHolds] using this
        exact h2.symm
    · rw [if_neg hij] at hfm; exact absurd hfm (by simp)
  · -- row constraint exactly_k (row i) 1
    obtain ⟨i, hir, rfl⟩ := List.mem_map.mp hrow
    rw [List.mem_range] at hir
    have hsi : swap01 i < 2 * m + 1 := swap01_lt _ _ (by omega) hir
    show satisfiesConstraintInt (IntConstraint.exactly_k
      ((List.range (2 * m + 1)).map (fun j => i * (2 * m + 1) + j)) 1) (a ∘ matchPerm m hm)
    have hmem : IntConstraint.exactly_k
        ((List.range (2 * m + 1)).map (fun j => swap01 i * (2 * m + 1) + j)) 1
        ∈ (gen_matching m).constraints :=
      List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨swap01 i, List.mem_range.mpr hsi, rfl⟩))
    have he := hsol _ hmem
    simp only [satisfiesConstraintInt, patternHolds] at he ⊢
    show (List.map (valAt (a ∘ matchPerm m hm))
      ((List.range (2 * m + 1)).map (fun j => i * (2 * m + 1) + j))).sum = ((1 : ℕ) : ℤ)
    have hmap : ((List.range (2 * m + 1)).map (fun j => i * (2 * m + 1) + j)).map
                  (valAt (a ∘ matchPerm m hm))
              = (((List.range (2 * m + 1)).map (fun j => i * (2 * m + 1) + j)).map (matchSwap m)).map
                  (valAt a) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro j hj
      rw [List.mem_range] at hj
      simp only [Function.comp_apply]
      exact valAt_swap m hm a _ (by nlinarith [hir, hj])
    rw [hmap, (row_swap m i hm |>.map (valAt a)).sum_eq]
    exact he

/-! ### The symmetry-breaking constraint is sound -/

theorem matching_sb_is_variable_symmetry_breaking (m : ℕ) (hm : 1 ≤ m) :
    variableSymmetryBreakingConstraint (gen_matching m) (matching_sb m) := by
  have h2 : (2 : ℕ) < (2 * m + 1) * (2 * m + 1) := by nlinarith [hm]
  have hs2 : matchSwap m 2 < (2 * m + 1) * (2 * m + 1) := matchSwap_lt m 2 hm h2
  intro a hsol
  by_cases hle : valAt a 2 ≤ valAt a (matchSwap m 2)
  · refine ⟨Equiv.refl _, VariableSymmetry.identity_is_symmetry _, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · show satisfiesConstraintInt (matching_sb m) (a ∘ Equiv.refl _)
      simp only [matching_sb, satisfiesConstraintInt, patternHolds, Equiv.coe_refl]
      exact hle
    · exact hsol c hmem
  · refine ⟨matchPerm m hm, match_is_variable_symmetry m hm, ?_⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hmem
    · show satisfiesConstraintInt (matching_sb m) (a ∘ matchPerm m hm)
      simp only [matching_sb, satisfiesConstraintInt, patternHolds]
      rw [show valAt (a ∘ matchPerm m hm) 2 = valAt a (matchSwap m 2) from valAt_swap m hm a 2 h2,
          show valAt (a ∘ matchPerm m hm) (matchSwap m 2)
            = valAt a (matchSwap m (matchSwap m 2)) from valAt_swap m hm a (matchSwap m 2) hs2,
          matchSwap_invol m 2 hm h2]
      omega
    · exact match_is_variable_symmetry m hm a hsol c hmem

theorem matching_unsat_of_var (m : ℕ) (hm : 1 ≤ m)
    (h_unsat : ¬ isSatisfiableInt ((gen_matching m).addConstraint (matching_sb m))) :
    ¬ isSatisfiableInt (gen_matching m) :=
  unsat_of_variable_sbc (gen_matching m) (matching_sb m)
    (matching_sb_is_variable_symmetry_breaking m hm) h_unsat

end CSP.L2S.PB.MatchingSB
