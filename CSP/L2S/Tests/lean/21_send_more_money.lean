import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Equivalence
import CSP.L2S.Symmetry
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# SEND + MORE = MONEY

Cryptarithmetic: each letter is a unique digit 0-9.
Variables: S, E, N, D, M, O, R, Y with alldifferent + leading digits ≠ 0.
Linear equation: 1000S + 91E - 90N + D - 9000M - 900O + 10R - Y = 0
-/

def allVars8 : _root_.Vector (VarType 8) 8 :=
  _root_.Vector.ofFn id

def send_more_money : IntCSP :=
  let bounds_list := (List.finRange 8).map fun i => bound i 0 9
  let alldiff := alldifferent allVars8
  let s_nonzero := not_equals_const ⟨0, by decide⟩ 0
  let m_nonzero := not_equals_const ⟨4, by decide⟩ 0
  let coeffs : _root_.Vector ℤ 8 := ⟨#[1000, 91, -90, 1, -9000, -900, 10, -1], rfl⟩
  let equation := linear_eq allVars8 coeffs 0
  ⟨8, bounds_list ++ [alldiff, s_nonzero, m_nonzero, equation]⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed send_more_money
