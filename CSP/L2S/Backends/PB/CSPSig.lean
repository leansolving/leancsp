/-
PB backend — the encoder's variable signature (`CSPSig`).

A PB encoding has a fixed set of integer variables (each with a per-variable
finite integer domain given as a sorted list), Boolean variables, and auxiliary
variables (for Tseitin/reification).  See PLAN.md §4.1.
-/
import Mathlib.Data.List.Sort

namespace CSP.L2S.PB

/-- Signature of a PB encoding: variable counts and per-variable domains. -/
structure CSPSig where
  /-- Number of integer variables. -/
  nInt   : Nat
  /-- Number of Boolean variables. -/
  nBool  : Nat
  /-- Number of auxiliary (Tseitin/reification) variables. -/
  nAux   : Nat
  /-- The finite domain of each integer variable, as a strictly sorted value list. -/
  values : Fin nInt → List Int
  /-- Each domain is strictly increasing (hence duplicate-free and canonical).
      `List.Pairwise (· < ·)` is the strictly-sorted predicate (Mathlib 4.30
      removed the `List.Sorted` abbreviation in favour of `Pairwise`). -/
  sorted : ∀ i, (values i).Pairwise (· < ·)
  /-- Each domain is nonempty. -/
  nonempty : ∀ i, 0 < (values i).length

namespace CSPSig

variable (S : CSPSig)

/-- Number of threshold variables for integer variable `i`: `|domain| − 1`.
    (The "`x ≤ max`" threshold is always true and is not represented.) -/
def width (i : Fin S.nInt) : Nat := (S.values i).length - 1

/-- The `j`-th domain value of integer variable `i`. -/
def valueAt (i : Fin S.nInt) (j : Fin (S.values i).length) : Int :=
  (S.values i).get j

/-- Maximum of integer variable `i`'s domain (its last, largest value). -/
def maxVal (i : Fin S.nInt) : Int :=
  (S.values i).getLast (List.ne_nil_of_length_pos (S.nonempty i))

end CSPSig

end CSP.L2S.PB
