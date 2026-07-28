import CSP.L2S.Backends.PB.PBVar
import CSP.L2S.Backends.PB.Core
import Mathlib.Order.Monotone.Basic

namespace CSP.L2S.PB

/-!
# PB backend — the `PBVar → Nat` bridge

The encoder builds constraints over the typed `PBVar S`; PBLean's kernel
constraint type is monomorphic over `Nat`.  This file injects `PBVar S` into `Nat`
with a flat layout `[ Boolean vars | thresholds (by variable) | aux ]`, proves the
injection injective, maps `PBConstr (PBVar S)` to `Sat.PB.Constr`, and proves the
bridge: if the `Nat`-mapped constraints are `formulaUnsat`, no typed valuation
satisfies all the typed constraints.
-/

variable {S : CSPSig}

/-! ### Threshold offsets (cumulative variable widths) -/

namespace CSPSig
variable (S : CSPSig)

/-- Width of integer variable `i` as a total `ℕ → ℕ` map (`0` out of range). -/
def widthN (i : Nat) : Nat := if h : i < S.nInt then S.width ⟨i, h⟩ else 0

/-- Cumulative threshold offset: total number of threshold variables belonging to
    integer variables with index `< i`. -/
def offsetThr (i : Nat) : Nat := ((List.range i).map S.widthN).sum

/-- Total number of threshold variables. -/
def totalThr : Nat := S.offsetThr S.nInt

/-- The offset for `i + 1` extends the offset for `i` by the width of variable `i`. -/
theorem offsetThr_succ (i : Nat) : S.offsetThr (i + 1) = S.offsetThr i + S.widthN i := by
  simp [offsetThr, List.range_succ]

/-- Threshold offsets are monotone in the variable index. -/
theorem offsetThr_mono : Monotone S.offsetThr := by
  apply monotone_nat_of_le_succ
  intro n; rw [offsetThr_succ]; omega

end CSPSig

/-! ### The injection -/

/-- Inject `PBVar S` into `Nat` with the flat layout
    `[ bool b ↦ b | thr i j ↦ nBool + offsetThr i + j | aux k ↦ nBool + totalThr + k ]`. -/
def PBVar.toNat : PBVar S → Nat
  | .bool b   => b.val
  | .thr i j  => S.nBool + S.offsetThr i.val + j.val
  | .aux k    => S.nBool + S.totalThr + k.val

/-- A threshold's offset lands strictly inside the threshold block. -/
theorem PBVar.thr_offset_lt (i : Fin S.nInt) (j : Fin (S.width i)) :
    S.offsetThr i.val + j.val < S.totalThr := by
  have hi : i.val < S.nInt := i.isLt
  have hj : (j : Nat) < S.widthN i.val := by
    rw [CSPSig.widthN, dif_pos i.isLt]; exact j.isLt
  have hs := S.offsetThr_succ i.val
  have hm : S.offsetThr (i.val + 1) ≤ S.offsetThr S.nInt := S.offsetThr_mono (by omega)
  unfold CSPSig.totalThr
  omega

/-- The `Nat` index map on PB variables is injective. -/
theorem PBVar.toNat_injective : Function.Injective (@PBVar.toNat S) := by
  intro x y hxy
  cases x with
  | bool b =>
    cases y with
    | bool b'  => exact congrArg PBVar.bool (Fin.ext (by simpa [PBVar.toNat] using hxy))
    | thr i' j' => exfalso; have := b.isLt; simp only [PBVar.toNat] at hxy; omega
    | aux k'   => exfalso; have := b.isLt; simp only [PBVar.toNat] at hxy; omega
  | thr i j =>
    cases y with
    | bool b'  => exfalso; have := b'.isLt; simp only [PBVar.toNat] at hxy; omega
    | thr i' j' =>
      simp only [PBVar.toNat] at hxy
      have hj  : (j : Nat) < S.widthN i.val := by
        rw [CSPSig.widthN, dif_pos i.isLt]; exact j.isLt
      have hj' : (j' : Nat) < S.widthN i'.val := by
        rw [CSPSig.widthN, dif_pos i'.isLt]; exact j'.isLt
      have key : i.val = i'.val := by
        rcases lt_trichotomy i.val i'.val with h | h | h
        · have hs := S.offsetThr_succ i.val
          have hm : S.offsetThr (i.val + 1) ≤ S.offsetThr i'.val := S.offsetThr_mono (by omega)
          omega
        · exact h
        · have hs := S.offsetThr_succ i'.val
          have hm : S.offsetThr (i'.val + 1) ≤ S.offsetThr i.val := S.offsetThr_mono (by omega)
          omega
      have hi : i = i' := Fin.ext key
      subst hi
      exact congrArg (PBVar.thr i) (Fin.ext (by omega))
    | aux k'   =>
      exfalso
      have := PBVar.thr_offset_lt i j
      simp only [PBVar.toNat] at hxy; omega
  | aux k =>
    cases y with
    | bool b'  => exfalso; have := b'.isLt; simp only [PBVar.toNat] at hxy; omega
    | thr i' j' =>
      exfalso
      have := PBVar.thr_offset_lt i' j'
      simp only [PBVar.toNat] at hxy; omega
    | aux k'   => exact congrArg PBVar.aux (Fin.ext (by simpa [PBVar.toNat] using hxy))

/-! ### Mapping constraints to `Sat.PB.Constr` -/

/-- Map a typed literal to a `Nat`-variable PBLean literal. -/
def Lit.toNatLit : Lit (PBVar S) → Sat.PB.Literal
  | .pos x => .pos x.toNat
  | .neg x => .neg x.toNat

/-- Map a typed constraint to a PBLean kernel constraint (coefficients/degree
    unchanged; variables injected via `toNat`). -/
def PBConstr.toNatConstr (c : PBConstr (PBVar S)) : Sat.PB.Constr :=
  { terms := c.terms.map (fun p => (p.1, p.2.toNatLit)), degree := c.degree }

/-! ### Sat-preservation and the unsat bridge -/

variable {w : Sat.PB.Valuation} {v : PBVar S → Bool}

/-- The `Nat`-mapped literal evaluates identically to the typed literal. -/
theorem evalLit_toNatLit (hw : ∀ x : PBVar S, w x.toNat = v x) (ℓ : Lit (PBVar S)) :
    Sat.PB.evalLit w ℓ.toNatLit = evalLit v ℓ := by
  cases ℓ with
  | pos x => simp [Lit.toNatLit, Sat.PB.evalLit, evalLit, hw x]
  | neg x => simp [Lit.toNatLit, Sat.PB.evalLit, evalLit, hw x]

/-- The `Nat`-mapped term sum evaluates identically to the typed term sum. -/
theorem evalSum_toNatConstr (hw : ∀ x : PBVar S, w x.toNat = v x)
    (ts : List (Term (PBVar S))) :
    Sat.PB.evalSum w (ts.map (fun p => (p.1, p.2.toNatLit))) = evalSum v ts := by
  induction ts with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨a, ℓ⟩ := hd
    simp [Sat.PB.evalSum, evalSum, evalLit_toNatLit hw, ih]

/-- The `Nat`-mapped constraint is satisfied by `w` iff the typed one is by `v`. -/
theorem toNatConstr_sat (hw : ∀ x : PBVar S, w x.toNat = v x) (c : PBConstr (PBVar S)) :
    (c.toNatConstr).sat w ↔ c.sat v := by
  simp only [Sat.PB.Constr.sat, PBConstr.sat, PBConstr.toNatConstr, evalSum_toNatConstr hw]

open Classical in
/-- A `Nat`-valuation agreeing with `v` on the encoded variables (`false`
    off-range; `toNat`-injectivity makes the on-range value well-defined). -/
noncomputable def liftVal (v : PBVar S → Bool) : Sat.PB.Valuation :=
  fun n => if h : ∃ x : PBVar S, x.toNat = n then v h.choose else false

theorem liftVal_toNat (v : PBVar S → Bool) (x : PBVar S) : liftVal v x.toNat = v x := by
  have hex : ∃ y : PBVar S, y.toNat = x.toNat := ⟨x, rfl⟩
  have hred : liftVal v x.toNat = v hex.choose := by unfold liftVal; rw [dif_pos hex]
  rw [hred]
  congr 1
  exact PBVar.toNat_injective hex.choose_spec

/-- **The unsat bridge.** If the `Nat`-mapped constraints are `formulaUnsat`, then
    no typed valuation satisfies all the typed constraints. -/
theorem unsat_bridge (cs : Array (PBConstr (PBVar S)))
    (hunsat : VeriPB.Reflect.formulaUnsat (cs.map PBConstr.toNatConstr))
    (v : PBVar S → Bool) :
    ∃ c ∈ cs.toList, ¬ c.sat v := by
  obtain ⟨c', hc', hnc'⟩ := hunsat (liftVal v)
  simp only [Array.toList_map, List.mem_map] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  exact ⟨c, hc, fun hsat => hnc' ((toNatConstr_sat (liftVal_toNat v) c).mpr hsat)⟩

end CSP.L2S.PB
