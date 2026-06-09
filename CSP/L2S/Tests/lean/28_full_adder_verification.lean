import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# Full Adder Circuit Verification (Pure Logic)

Full adder: (a, b, cin) → (sum, cout)

Circuit definition using only logical operations:
- sum = a ⊕ b ⊕ cin (3-way XOR)
- cout = (a∧b) ∨ (a∧cin) ∨ (b∧cin) (majority via AND/OR)

Variables:
- v0=a, v1=b, v2=cin (inputs)
- v3=sum, v4=cout (outputs)
- v5=ab, v6=ac, v7=bc (AND gates for majority)

Result: 8 variables, 6 constraints
-/

def full_adder_verification : IntCSP :=
  let nvars := 8
  let bounds := (List.finRange nvars).map fun i => bound i 0 1

  -- sum = a ⊕ b ⊕ cin
  let sum_def := xor_all ⟨#[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩], rfl⟩ ⟨3, by decide⟩

  -- cout = (a∧b) ∨ (a∧cin) ∨ (b∧cin)
  let ab := and_gate ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨5, by decide⟩
  let ac := and_gate ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨6, by decide⟩
  let bc := and_gate ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨7, by decide⟩
  let cout_def := or_all ⟨#[⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩], rfl⟩ ⟨4, by decide⟩

  -- Negated correctness: a + b + cin ≠ 2·cout + sum
  let neg_prop := linear_ne
    ⟨#[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨3, by decide⟩], rfl⟩
    ⟨#[1, 1, 1, -2, -1], rfl⟩
    0

  ⟨nvars, bounds ++ [sum_def, ab, ac, bc, cout_def, neg_prop]⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed full_adder_verification
