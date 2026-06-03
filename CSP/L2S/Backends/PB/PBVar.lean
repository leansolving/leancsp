/-
PB backend — the typed propositional variable `PBVar S` and the smart
threshold-literal constructor `mkLeLit`.
-/
import CSP.L2S.Backends.PB.CSPSig
import CSP.L2S.Backends.PB.PBConstr

namespace CSP.L2S.PB

open CSPSig

/-- Propositional variables of the PB (order-)encoding of a signature `S`:

  * `bool b`  — an original Boolean CSP variable;
  * `thr i j` — a threshold variable meaning "integer variable `i` is
                **at most** its `j`-th domain value `valuesᵢ[j]`";
  * `aux k`   — a Tseitin/reification auxiliary.

  The type is **finite** (no `Nat` constructors) and only valid thresholds
  (`j : Fin (width i)`) can be named, so OPB serialization sees a closed
  variable count and out-of-range thresholds are unconstructible. -/
inductive PBVar (S : CSPSig) where
  | bool : Fin S.nBool → PBVar S
  | thr  : (i : Fin S.nInt) → Fin (S.width i) → PBVar S
  | aux  : Fin S.nAux → PBVar S
  deriving DecidableEq, Repr, Hashable

/-- A literal-or-constant.  Paper-level "`xᵢ ≤ k`" thresholds may fall outside
    the domain (k below the minimum, or k at/above the maximum); those have no
    corresponding `thr` variable and collapse to a Boolean constant. -/
inductive LitConst (V : Type) where
  | lit   : Lit V → LitConst V
  | const : Bool → LitConst V
  deriving Repr

namespace LitConst

variable (S : CSPSig)

/-- Smart constructor for the literal denoting "`xᵢ ≤ k`":

  * `k ≥ max(Dᵢ)`  → `const true`   (no domain value exceeds `k`);
  * `k < min(Dᵢ)`  → `const false`  (the smallest value already exceeds `k`);
  * otherwise      → the threshold variable for the largest domain value `≤ k`.

  Implementation: `findIdx? (· > k)` returns the first index whose value
  exceeds `k`.  `none` ⇒ all values `≤ k`; `some 0` ⇒ even the smallest exceeds
  `k`; `some (j+1)` ⇒ index `j` is the largest with value `≤ k`, so threshold
  `thr i j` (when `j < width i`; the boundary `j = width i` is `x ≤ max`, always
  true). -/
def mkLeLit (i : Fin S.nInt) (k : Int) : LitConst (PBVar S) :=
  match (S.values i).findIdx? (· > k) with
  | none        => .const true
  | some 0      => .const false
  | some (j + 1) =>
      if hj : j < S.width i then
        .lit (.pos (.thr i ⟨j, hj⟩))
      else
        .const true

end LitConst

end CSP.L2S.PB
