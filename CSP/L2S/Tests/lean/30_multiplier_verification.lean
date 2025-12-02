import CSP.L2S.Core
import CSP.L2S.Constraints
import CSP.L2S.Tests.TestHelpersTimed

open CSP.L2S
open CSP.L2S.Tests.Timed

/-!
# 2-Bit × 2-Bit Multiplier Verification (Specification-Level)

Specification: (2*a1 + a0) × (2*b1 + b0) = 8*p3 + 4*p2 + 2*p1 + p0

Variables:
- v0,v1: a0,a1 (inputs)
- v2,v3: b0,b1 (inputs)
- v4..v7: pp00,pp01,pp10,pp11 (DUT partial products)
- v8: c1 (DUT half-adder carry)
- v9..v12: p0,p1,p2,p3 (DUT outputs)
- v13: sum_a = 2*a1 + a0
- v14: sum_b = 2*b1 + b0
- v15: spec_product = sum_a * sum_b

Total: 16 variables
-/

def multiplier_2bit : HomogeneousCSP :=
  let nvars := 16
  let bounds := (List.finRange nvars).map fun i => bound i 0 1

  -- DUT (Device Under Test): actual multiplier circuit implementation
  let pp00 := and_gate ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨4, by decide⟩
  let pp01 := and_gate ⟨0, by decide⟩ ⟨3, by decide⟩ ⟨5, by decide⟩
  let pp10 := and_gate ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨6, by decide⟩
  let pp11 := and_gate ⟨1, by decide⟩ ⟨3, by decide⟩ ⟨7, by decide⟩

  -- p0 = pp00 (wire connection)
  let p0_conn := iff ⟨9, by decide⟩ ⟨4, by decide⟩

  -- Half adder 1: pp01 + pp10 → (p1, c1)
  let ha1_sum := xor_gate ⟨5, by decide⟩ ⟨6, by decide⟩ ⟨10, by decide⟩
  let ha1_carry := and_gate ⟨5, by decide⟩ ⟨6, by decide⟩ ⟨8, by decide⟩

  -- Half adder 2: pp11 + c1 → (p2, p3)
  let ha2_sum := xor_gate ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨11, by decide⟩
  let ha2_carry := and_gate ⟨7, by decide⟩ ⟨8, by decide⟩ ⟨12, by decide⟩

  -- Specification constraints (high-level arithmetic)
  -- v13 = sum_a = 2*a1 + a0
  let sum_a_def := linear_eq_var
    ⟨#[⟨1, by decide⟩, ⟨0, by decide⟩], rfl⟩
    ⟨#[2, 1], rfl⟩
    ⟨13, by decide⟩

  -- v14 = sum_b = 2*b1 + b0
  let sum_b_def := linear_eq_var
    ⟨#[⟨3, by decide⟩, ⟨2, by decide⟩], rfl⟩
    ⟨#[2, 1], rfl⟩
    ⟨14, by decide⟩

  -- v15 = spec_product = sum_a * sum_b
  let product_def := product_eq_var
    ⟨#[⟨13, by decide⟩, ⟨14, by decide⟩], rfl⟩
    ⟨15, by decide⟩

  -- Negated property: 8*p3 + 4*p2 + 2*p1 + p0 - spec_product ≠ 0
  -- Equivalently: spec_product ≠ 8*p3 + 4*p2 + 2*p1 + p0
  let violation := linear_ne_var
    ⟨#[⟨12, by decide⟩, ⟨11, by decide⟩, ⟨10, by decide⟩, ⟨9, by decide⟩], rfl⟩
    ⟨#[8, 4, 2, 1], rfl⟩
    ⟨15, by decide⟩

  ⟨nvars, bounds ++ [
    pp00, pp01, pp10, pp11, p0_conn,
    ha1_sum, ha1_carry, ha2_sum, ha2_carry,
    sum_a_def, sum_b_def, product_def, violation
  ]⟩

def main : IO Unit := do
  saveAllBackendsAutoTimed multiplier_2bit
