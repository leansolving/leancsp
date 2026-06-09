import CSP.L2S.Backends.PB.NotAllEqualBridge

namespace CSP.L2S.PB

open CSP.L2S

/-!
# PB backend — reusable circuit-gate bridges (test-file-free)

Generic `{nv}`-arity bridges from a corpus logic-gate `dynamic` checker to the
arithmetic fact a PB encoding consumes, plus the pure-`ℤ` full-adder identity.

These live in their own module (importing no `Tests/lean/NN_*` corpus file) so that
*multiple* circuit-instance files can share them: each corpus generator defines its own
`main`, so two corpus files cannot be co-imported (environment clash).  `FullAdder.lean`
(corpus `28`) and `RippleCarry.lean` (corpus `29`) both consume these.

* `xor_all3_sat` — a ternary `xor_all` gives `(a v0 + a v1 + a v2) % 2 = a r` (parity);
* `and_gate_sat` — a binary `and_gate` gives `a out = min (a in1) (a in2)`;
* `or_all3_full_sat` — a ternary `or_all` gives `a r = max (max (a g1) (a g2)) (a g3)`;
* `fa_identity` — over `{0,1}`, parity + 2·majority = sum, i.e. `v0+v1+v2 - v3 - 2·v4 = 0`.
-/

/-- **Bridge.** A satisfied ternary `xor_all [v0,v1,v2] r` gives `r = parity`, i.e.
    `(a v0 + a v1 + a v2) % 2 = a r`.  Reduces the `vars.sum % 2 = r` checker. -/
theorem xor_all3_sat {nv : ℕ} (v0 v1 v2 r : Fin nv) (a : IntAssignment nv)
    (h : IntCSP.satisfiesConstraintInt
      (xor_all (⟨#[v0, v1, v2], rfl⟩ : _root_.Vector (VarType nv) 3) r) a) :
    (a v0 + a v1 + a v2) % 2 = a r := by
  simp only [IntCSP.satisfiesConstraintInt, xor_all, patternHolds, map_valAt, valAt_eq] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] at h
  rw [add_assoc]; exact h

/-- **Bridge.** A satisfied binary `and_gate in1 in2 out` over `{0,1}` gives
    `out = min(in1, in2)` (the `dynamic` checker is `decide (z = min x y)`). -/
theorem and_gate_sat {nv : ℕ} (in1 in2 out : Fin nv) (a : IntAssignment nv)
    (h : IntCSP.satisfiesConstraintInt (and_gate in1 in2 out) a) :
    a out = min (a in1) (a in2) := by
  simp only [IntCSP.satisfiesConstraintInt, and_gate, patternHolds, valAt_eq] at h
  exact h

/-- **Bridge.** A satisfied ternary `or_all [g1,g2,g3] r` over `{0,1}` gives
    `r = max(max g1 g2) g3` (the `dynamic` checker is `r = foldl-max`; reconciled to
    nested `max` via a pure-`ℤ` helper). -/
theorem or_all3_full_sat {nv : ℕ} (g1 g2 g3 r : Fin nv) (a : IntAssignment nv)
    (h : IntCSP.satisfiesConstraintInt
      (or_all (⟨#[g1, g2, g3], rfl⟩ : _root_.Vector (VarType nv) 3) r) a) :
    a r = max (max (a g1) (a g2)) (a g3) := by
  simp only [IntCSP.satisfiesConstraintInt, or_all, patternHolds, map_valAt, valAt_eq] at h
  simp only [_root_.Vector.toList_mk, List.map_cons, List.map_nil, List.headI,
    List.foldl_cons, List.foldl_nil, ne_eq, lt_self_iff_false, if_false] at h
  obtain ⟨-, h⟩ := h
  have key : ∀ x y z : ℤ,
      (if z > (if y > x then y else x) then z else (if y > x then y else x))
        = max (max x y) z := by
    intro x y z; rw [max_def, max_def]; split_ifs <;> omega
  rw [h]; exact key (a g1) (a g2) (a g3)

/-- **The full-adder identity** (pure `ℤ`, `{0,1}³` enumeration): with `sum = parity`
    of `v0,v1,v2`, the AND outputs `v5,v6,v7` their pairwise `min`, and `cout = v4` the
    `max` of those, the carry-save identity `v0 + v1 + v2 - v3 - 2·v4 = 0` holds. -/
theorem fa_identity (v0 v1 v2 v3 v4 v5 v6 v7 : ℤ)
    (b0 : 0 ≤ v0) (b0' : v0 ≤ 1) (b1 : 0 ≤ v1) (b1' : v1 ≤ 1) (b2 : 0 ≤ v2) (b2' : v2 ≤ 1)
    (hx : (v0 + v1 + v2) % 2 = v3)
    (h5 : v5 = min v0 v1) (h6 : v6 = min v0 v2) (h7 : v7 = min v1 v2)
    (h4 : v4 = max (max v5 v6) v7) :
    v0 + v1 + v2 - v3 - 2 * v4 = 0 := by
  subst h5 h6 h7 h4
  rcases (by omega : v0 = 0 ∨ v0 = 1) with rfl | rfl <;>
  rcases (by omega : v1 = 0 ∨ v1 = 1) with rfl | rfl <;>
  rcases (by omega : v2 = 0 ∨ v2 = 1) with rfl | rfl <;>
    simp_all [min_def, max_def] <;> omega

end CSP.L2S.PB
