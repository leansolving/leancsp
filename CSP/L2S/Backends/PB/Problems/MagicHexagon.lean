import CSP.L2S.Backends.PB.GenericEncode
import CSP.L2S.Constraints

namespace CSP.L2S.PB.MagicHexagon

open CSP.L2S CSP.L2S.PB

/-!
# PB backend — end-to-end verified UNSAT for the order-2 magic hexagon

A normal magic hexagon of order `n` exists only for `n ∈ {1,3}`.  The smallest
impossible order is `n = 2`: seven cells filled with `1..7` (total `28`) split by each
of the three directions into three lines of common sum `M`, forcing `3M = 28` — a
divisibility contradiction native to cutting planes.

`magicHexagon2` carries seven cells over `{1..7}`, an `alldifferent`, the (redundant)
total-sum `= 28`, and the nine magic-line equalities — `alldifferent`, `sum`, and
`linear` constraints, all supported.  The proof is one `csp_unsat` over the committed
certificate (`certs/magic_2.pbp`); axioms clean.
-/

/-! ### The CSP -/

/-- The scope of the all-different and total-sum constraints: all seven cells. -/
def mhCellScope : _root_.Vector (VarType 7) 7 := ⟨#[0, 1, 2, 3, 4, 5, 6], rfl⟩

/-- Top row `{a,b} = {0,1}` equals the middle row `{c,d,e} = {2,3,4}`:
    `a 0 + a 1 − a 2 − a 3 − a 4 = 0`. -/
def mhTopEqMid : IntConstraint 7 :=
  linear_eq (⟨#[0, 1, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 5)
    (⟨#[1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 5) 0

/-- Bottom row `{f,g} = {5,6}` equals the middle row `{c,d,e} = {2,3,4}`:
    `a 5 + a 6 − a 2 − a 3 − a 4 = 0`. -/
def mhBotEqMid : IntConstraint 7 :=
  linear_eq (⟨#[5, 6, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 5)
    (⟨#[1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 5) 0

/-- The remaining six magic lines, each written as "line = middle row `{c,d,e}`". -/
def mhCrossLines : List (IntConstraint 7) :=
  [ -- "╲" diagonal {a,c} = {0,2}
    linear_eq (⟨#[0, 2, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 5)
      (⟨#[1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 5) 0,
    -- "╲" diagonal {b,d,f} = {1,3,5}
    linear_eq (⟨#[1, 3, 5, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 6)
      (⟨#[1, 1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 6) 0,
    -- "╲" diagonal {e,g} = {4,6}
    linear_eq (⟨#[4, 6, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 5)
      (⟨#[1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 5) 0,
    -- "╱" diagonal {b,e} = {1,4}
    linear_eq (⟨#[1, 4, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 5)
      (⟨#[1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 5) 0,
    -- "╱" diagonal {a,d,g} = {0,3,6}
    linear_eq (⟨#[0, 3, 6, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 6)
      (⟨#[1, 1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 6) 0,
    -- "╱" diagonal {c,f} = {2,5}
    linear_eq (⟨#[2, 5, 2, 3, 4], rfl⟩ : _root_.Vector (VarType 7) 5)
      (⟨#[1, 1, -1, -1, -1], rfl⟩ : _root_.Vector ℤ 5) 0 ]

/-- The order-2 magic hexagon as a `IntCSP`: seven cells over `{1 .. 7}`,
    `alldifferent`, the (redundant) total-sum `= 28`, and the nine line-equalities. -/
def magicHexagon2 : IntCSP :=
  ⟨7, ((List.finRange 7).map (fun i => bound i 1 7))
      ++ (alldifferent mhCellScope :: sum_eq mhCellScope 28
          :: mhTopEqMid :: mhBotEqMid :: mhCrossLines)⟩

/-- **The order-2 magic hexagon does not exist.** -/
theorem magic_hexagon_2_unsat : ¬ magicHexagon2.isSatisfiableInt :=
  csp_unsat_file magicHexagon2 42 "certs/magic_2.pbp"

end CSP.L2S.PB.MagicHexagon
