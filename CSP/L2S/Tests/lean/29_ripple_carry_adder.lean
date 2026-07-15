import CSP.L2S.Core
import CSP.L2S.Constraints

open CSP.L2S

/-!
# 4-Bit Ripple Carry Adder

Chains 4 full adders, each defined with pure logical operations.

Variables: 28 total
- v0..v3: a[0..3], v4..v7: b[0..3], v8..v11: s[0..3]
- v12: c0(=0), v13..v15: c[1..3], v16: cout
- v17..v28: auxiliary (3 ANDs per stage × 4 = 12)

Result: 28 variables, 22 constraints
-/

def ripple_carry_adder_4bit : IntCSP :=
  let nvars := 29
  let bounds := (List.finRange nvars).map fun i => bound i 0 1

  let c0_zero := equals_const ⟨12, by decide⟩ 0

  -- Stage 0: a0 + b0 + c0 → s0, c1
  let s0_sum := xor_all ⟨#[⟨0, by decide⟩, ⟨4, by decide⟩, ⟨12, by decide⟩], rfl⟩ ⟨8, by decide⟩
  let s0_ab := and_gate ⟨0, by decide⟩ ⟨4, by decide⟩ ⟨17, by decide⟩
  let s0_ac := and_gate ⟨0, by decide⟩ ⟨12, by decide⟩ ⟨18, by decide⟩
  let s0_bc := and_gate ⟨4, by decide⟩ ⟨12, by decide⟩ ⟨19, by decide⟩
  let s0_cout := or_all ⟨#[⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩], rfl⟩ ⟨13, by decide⟩

  -- Stage 1: a1 + b1 + c1 → s1, c2
  let s1_sum := xor_all ⟨#[⟨1, by decide⟩, ⟨5, by decide⟩, ⟨13, by decide⟩], rfl⟩ ⟨9, by decide⟩
  let s1_ab := and_gate ⟨1, by decide⟩ ⟨5, by decide⟩ ⟨20, by decide⟩
  let s1_ac := and_gate ⟨1, by decide⟩ ⟨13, by decide⟩ ⟨21, by decide⟩
  let s1_bc := and_gate ⟨5, by decide⟩ ⟨13, by decide⟩ ⟨22, by decide⟩
  let s1_cout := or_all ⟨#[⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩], rfl⟩ ⟨14, by decide⟩

  -- Stage 2: a2 + b2 + c2 → s2, c3
  let s2_sum := xor_all ⟨#[⟨2, by decide⟩, ⟨6, by decide⟩, ⟨14, by decide⟩], rfl⟩ ⟨10, by decide⟩
  let s2_ab := and_gate ⟨2, by decide⟩ ⟨6, by decide⟩ ⟨23, by decide⟩
  let s2_ac := and_gate ⟨2, by decide⟩ ⟨14, by decide⟩ ⟨24, by decide⟩
  let s2_bc := and_gate ⟨6, by decide⟩ ⟨14, by decide⟩ ⟨25, by decide⟩
  let s2_cout := or_all ⟨#[⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩], rfl⟩ ⟨15, by decide⟩

  -- Stage 3: a3 + b3 + c3 → s3, cout
  let s3_sum := xor_all ⟨#[⟨3, by decide⟩, ⟨7, by decide⟩, ⟨15, by decide⟩], rfl⟩ ⟨11, by decide⟩
  let s3_ab := and_gate ⟨3, by decide⟩ ⟨7, by decide⟩ ⟨26, by decide⟩
  let s3_ac := and_gate ⟨3, by decide⟩ ⟨15, by decide⟩ ⟨27, by decide⟩
  let s3_bc := and_gate ⟨7, by decide⟩ ⟨15, by decide⟩ ⟨28, by decide⟩
  let s3_cout := or_all ⟨#[⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩], rfl⟩ ⟨16, by decide⟩

  -- Negated correctness: A + B ≠ Result
  let violation := linear_ne
    ⟨#[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
       ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩,
       ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨16, by decide⟩], rfl⟩
    ⟨#[1, 2, 4, 8, 1, 2, 4, 8, -1, -2, -4, -8, -16], rfl⟩
    0

  ⟨nvars, bounds ++ [c0_zero] ++
    [s0_sum, s0_ab, s0_ac, s0_bc, s0_cout] ++
    [s1_sum, s1_ab, s1_ac, s1_bc, s1_cout] ++
    [s2_sum, s2_ab, s2_ac, s2_bc, s2_cout] ++
    [s3_sum, s3_ab, s3_ac, s3_bc, s3_cout] ++
    [violation]⟩
