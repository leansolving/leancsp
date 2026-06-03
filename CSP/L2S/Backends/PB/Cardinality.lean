import CSP.L2S.Backends.PB.SignedPB
import CSP.L2S.Backends.PB.Semantics

namespace CSP.L2S.PB

open scoped BigOperators

/-!
# PB backend — cardinality constraints (PLAN.md §6.6)

`at_most_k` / `at_least_k` / `exactly_k` over a list of **Boolean** CSP variables
are *native* pseudo-Boolean constraints — no order-encoding overhead:

* `Σ bᵢ ≥ k`            for `at_least_k`,
* `Σ ¬bᵢ ≥ n − k`       for `at_most_k`  (equivalent to `Σ bᵢ ≤ k`),
* both                  for `exactly_k`.

`boolCount v vars` is the number of true Booleans under `v`; each soundness lemma
says "the CSP cardinality fact on `boolCount` ⇒ the encoded PB constraint holds",
the forward direction the UNSAT pipeline needs.  These encoders use no auxiliary
variables, so (like `NotAllEqual.lean`) soundness is stated over an arbitrary
valuation `v`.
-/

variable {S : CSPSig}

/-- The number of `true` Booleans among `vars` under `v` (as an `Int`). -/
def boolCount (v : Valuation S) (vars : List (Fin S.nBool)) : Int :=
  (vars.map (fun i => if v (.bool i) then (1 : Int) else 0)).sum

/-! ### `signedEval` of a unit-coefficient literal list -/

/-- The signed sum of a list of weight-`1` literals is the sum of their integer
    `evalLit` values (generalizes the inline step in `NotAllEqual`). -/
theorem signedEval_unit_coeff {V : Type} (v : V → Bool) {α : Type} (L : List α)
    (f : α → Lit V) :
    signedEval v (L.map (fun i => ((1 : Int), f i)))
      = (L.map (fun i => (evalLit v (f i) : Int))).sum := by
  simp only [signedEval, List.map_map, Function.comp_def, one_mul]

/-- `Σ (1 − g i)` over a list telescopes to `length − Σ g i`. -/
private theorem list_sum_one_sub {α : Type} (L : List α) (g : α → Int) :
    (L.map (fun i => (1 : Int) - g i)).sum = (L.length : Int) - (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; push_cast; ring

/-- The all-positive unit sum over Booleans is exactly the true-count. -/
theorem signedEval_pos_bool (v : Valuation S) (vars : List (Fin S.nBool)) :
    signedEval v (vars.map (fun i => ((1 : Int), Lit.pos (PBVar.bool i)))) = boolCount v vars := by
  rw [signedEval_unit_coeff]
  unfold boolCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  by_cases h : v (.bool i) <;> simp [evalLit, h]

/-- The all-negative unit sum over Booleans is `n − true-count`. -/
theorem signedEval_neg_bool (v : Valuation S) (vars : List (Fin S.nBool)) :
    signedEval v (vars.map (fun i => ((1 : Int), Lit.neg (PBVar.bool i))))
      = (vars.length : Int) - boolCount v vars := by
  rw [signedEval_unit_coeff]
  unfold boolCount
  rw [show (vars.map (fun i => (evalLit v (Lit.neg (PBVar.bool i)) : Int)))
        = vars.map (fun i => (1 : Int) - (if v (.bool i) then (1 : Int) else 0)) from ?_]
  · rw [list_sum_one_sub]
  · apply List.map_congr_left
    intro i _
    by_cases h : v (.bool i) <;> simp [evalLit, h]

/-! ### The encoders -/

/-- `at_most_k`: `Σ ¬bᵢ ≥ n − k`, i.e. at most `k` of the Booleans are true. -/
def encodeAtMostK (vars : List (Fin S.nBool)) (k : Nat) : SignedPBConstr (PBVar S) where
  terms := vars.map (fun i => ((1 : Int), Lit.neg (PBVar.bool i)))
  rhs := (vars.length : Int) - k

/-- `at_least_k`: `Σ bᵢ ≥ k`, i.e. at least `k` of the Booleans are true. -/
def encodeAtLeastK (vars : List (Fin S.nBool)) (k : Nat) : SignedPBConstr (PBVar S) where
  terms := vars.map (fun i => ((1 : Int), Lit.pos (PBVar.bool i)))
  rhs := k

/-- `exactly_k`: both the `at_most_k` and `at_least_k` constraints. -/
def encodeExactlyK (vars : List (Fin S.nBool)) (k : Nat) : List (SignedPBConstr (PBVar S)) :=
  [encodeAtMostK vars k, encodeAtLeastK vars k]

/-! ### Soundness -/

/-- **Soundness.** If at least `k` of the Booleans are true, `encodeAtLeastK` holds. -/
theorem encodeAtLeastK_sound (v : Valuation S) (vars : List (Fin S.nBool)) (k : Nat)
    (h : (k : Int) ≤ boolCount v vars) : (encodeAtLeastK vars k).sat v := by
  show signedEval v (vars.map (fun i => ((1 : Int), Lit.pos (PBVar.bool i)))) ≥ (k : Int)
  rw [signedEval_pos_bool]; exact h

/-- **Soundness.** If at most `k` of the Booleans are true, `encodeAtMostK` holds. -/
theorem encodeAtMostK_sound (v : Valuation S) (vars : List (Fin S.nBool)) (k : Nat)
    (h : boolCount v vars ≤ (k : Int)) : (encodeAtMostK vars k).sat v := by
  show signedEval v (vars.map (fun i => ((1 : Int), Lit.neg (PBVar.bool i))))
    ≥ (vars.length : Int) - k
  rw [signedEval_neg_bool]; omega

/-- **Soundness.** If exactly `k` of the Booleans are true, both `encodeExactlyK`
    constraints hold. -/
theorem encodeExactlyK_sound (v : Valuation S) (vars : List (Fin S.nBool)) (k : Nat)
    (h : boolCount v vars = (k : Int)) :
    ∀ c ∈ encodeExactlyK vars k, c.sat v := by
  intro c hc
  simp only [encodeExactlyK, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact encodeAtMostK_sound v vars k h.le
  · exact encodeAtLeastK_sound v vars k h.ge

/-! ### Unit test: a concrete 2-Boolean signature -/

namespace CardinalityTest

/-- Tiny signature: no integer variables, two Boolean variables. -/
def sig2 : CSPSig where
  nInt := 0
  nBool := 2
  nAux := 0
  values := fun i => i.elim0
  sorted := fun i => i.elim0
  nonempty := fun i => i.elim0

/-- The valuation `b₀ = true`, `b₁ = false` (one true Boolean). -/
def v2 : Valuation sig2
  | .bool i => decide (i.val = 0)
  | .thr i _ => i.elim0
  | .aux i => i.elim0

/-- The two Boolean variables `[b₀, b₁]` (raw `Fin.mk` avoids the projection-`OfNat`
    synthesis friction of `[0, 1] : List (Fin sig2.nBool)`; cf. MEM_002 #12). -/
def bs : List (Fin sig2.nBool) := [⟨0, by decide⟩, ⟨1, by decide⟩]

example : boolCount v2 bs = 1 := by decide
example : (encodeAtMostK bs 1).sat v2 := encodeAtMostK_sound v2 bs 1 (by decide)
example : (encodeAtLeastK bs 1).sat v2 := encodeAtLeastK_sound v2 bs 1 (by decide)
example : ∀ c ∈ encodeExactlyK bs 1, c.sat v2 := encodeExactlyK_sound v2 bs 1 (by decide)

end CardinalityTest

end CSP.L2S.PB
