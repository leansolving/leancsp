import Mathlib.Data.List.Basic

namespace CSP.L2S.PB

/-!
# PB backend — polymorphic pseudo-Boolean constraint mirror

PBLean's kernel constraint type is monomorphic over `Nat`, but the encoder builds
constraints over the typed `PBVar S` so that only valid thresholds can be named.
`PBConstr V` is a structurally identical polymorphic mirror with the same
`Σ aᵢ·lᵢ ≥ degree` semantics; `ToNat.lean` collapses `V := PBVar S` to `Nat`.
-/

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

/-- A literal evaluates to at most `1`. -/
theorem evalLit_le_one (v : V → Bool) (ℓ : Lit V) : evalLit v ℓ ≤ 1 := by
  cases ℓ <;> simp only [evalLit] <;> split <;> omega

/-- A literal and its negation evaluate to `1` together. -/
theorem evalLit_negate_add (v : V → Bool) (ℓ : Lit V) :
    evalLit v ℓ + evalLit v ℓ.negate = 1 := by
  cases ℓ <;> simp only [evalLit, Lit.negate] <;> split <;> simp

/-- `evalSum` distributes over list append. -/
theorem evalSum_append (v : V → Bool) (a b : List (Term V)) :
    evalSum v (a ++ b) = evalSum v a + evalSum v b := by
  induction a with
  | nil => simp [evalSum]
  | cons hd tl ih => obtain ⟨c, ℓ⟩ := hd; simp only [List.cons_append, evalSum, ih, Nat.add_assoc]

end CSP.L2S.PB
