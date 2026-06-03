/-
PB backend — polymorphic pseudo-Boolean constraint mirror.

PBLean's kernel constraint type `Sat.PB.Constr` is **monomorphic** over `Nat`
variables.  The encoder, however, builds constraints over the *typed* variable
type `PBVar S` (so that only valid threshold variables can be named).  This file
provides a structurally identical, *polymorphic* mirror `PBConstr V` with the
same `Σ aᵢ·lᵢ ≥ degree` semantics.  The `ToOPB` bridge (PLAN §8) later collapses
`V := PBVar S` to `Nat` via an injection, mapping `PBConstr (PBVar S)` to
`Sat.PB.Constr`; because the two types are structurally identical, that map and
its `sat`-preservation are mechanical.
-/
import Mathlib.Data.List.Basic

namespace CSP.L2S.PB

variable {V : Type}

/-- A pseudo-Boolean literal over an abstract variable type `V`
    (mirror of `Sat.PB.Literal`, which is monomorphic on `Nat`). -/
inductive Lit (V : Type) where
  | pos : V → Lit V
  | neg : V → Lit V
  deriving DecidableEq, Repr

namespace Lit

/-- The underlying variable of a literal. -/
def var : Lit V → V
  | .pos x => x
  | .neg x => x

/-- Flip a literal's polarity. -/
def negate : Lit V → Lit V
  | .pos x => .neg x
  | .neg x => .pos x

end Lit

/-- A weighted literal term: a non-negative coefficient paired with a literal. -/
abbrev Term (V : Type) := Nat × Lit V

/-- Evaluate a literal under a Boolean valuation: `1` if satisfied, `0` otherwise. -/
def evalLit (v : V → Bool) : Lit V → Nat
  | .pos x => if v x then 1 else 0
  | .neg x => if v x then 0 else 1

/-- Evaluate a sum of weighted literal terms under a valuation. -/
def evalSum (v : V → Bool) : List (Term V) → Nat
  | [] => 0
  | (c, l) :: rest => c * evalLit v l + evalSum v rest

/-- A pseudo-Boolean constraint `Σ aᵢ·lᵢ ≥ degree` over variables `V`. -/
structure PBConstr (V : Type) where
  /-- The weighted literal terms. -/
  terms  : List (Term V)
  /-- The right-hand-side degree. -/
  degree : Nat
  deriving Repr

/-- A constraint is satisfied when its weighted sum meets the degree. -/
def PBConstr.sat (v : V → Bool) (c : PBConstr V) : Prop :=
  c.degree ≤ evalSum v c.terms

end CSP.L2S.PB
