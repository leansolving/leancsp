import CSP.L2S.Backends.PB.Extend
import Mathlib.Algebra.Order.Ring.Abs

namespace CSP.L2S.PB

open CSPSig
open scoped BigOperators

/-!
# PB backend — general linear disequality `Σ aᵢ·xᵢ ≠ b` via a Big-M selector (PLAN §6.4)

The aux-free `≠` special cases (variable ≠ constant `encodeNeConst`, variable ≠
variable `encodeAllDifferent [i,j]`) live in `AllDifferent.lean`.  The **general**
linear disequality `Σ aᵢ·xᵢ ≠ b` is genuinely disjunctive — `Σ ≤ b−1 ∨ Σ ≥ b+1` —
so it needs a fresh Boolean **selector** `s` (an `aux` variable) plus the Big-M
construction:

* `s = false ⇒ Σ ≤ b−1`   encoded as   `Σ ≤ (b−1) + M·⟦s⟧`
* `s = true  ⇒ Σ ≥ b+1`   encoded as   `Σ ≥ (b+1) − M·(1−⟦s⟧)`

with `M` large enough that the *unselected* branch is vacuous.  We take
`M = Σᵢ |aᵢ|·maxAbsᵢ + |b| + 1`, where `maxAbsᵢ = max(|minVal i|, |maxVal i|)`
bounds `|xᵢ|`; this dominates `|Σ aᵢ·xᵢ − b|` for every in-domain assignment
(`linear_abs_bound`).

This is the **first aux-using encoder**: it supplies the aux-setter
`auxOf a := s ↦ decide(Σ aᵢ·a(xᵢ) > b)` to the generic spine `csp_unsat_generic`
through the bridge `extend_sat_encodeLinearNe`, so the selector is set from the
solution.  Both Big-M constraints are built by appending one aux-literal term to a
reused `encodeLinearLe`, so soundness rides on `encodeLinearLe`'s substitution
identity plus the `linear_abs_bound` range fact.
-/

variable {S : CSPSig}

/-! ### Generic helpers: appending an aux term, and the encode-sum identity -/

/-- Append a single (aux) literal term `(coeff, ℓ)` to a signed constraint, keeping
    the right-hand side.  Used to splice the Big-M selector term into a reused
    linear encoding. -/
def SignedPBConstr.addTerm {V : Type} (c : SignedPBConstr V) (coeff : Int) (ℓ : Lit V) :
    SignedPBConstr V :=
  { c with terms := c.terms ++ [(coeff, ℓ)] }

/-- The signed sum gains exactly the appended term. -/
theorem signedEval_addTerm {V : Type} (v : V → Bool) (c : SignedPBConstr V)
    (coeff : Int) (ℓ : Lit V) :
    signedEval v (c.addTerm coeff ℓ).terms
      = signedEval v c.terms + coeff * (evalLit v ℓ : Int) := by
  rw [SignedPBConstr.addTerm]
  show signedEval v (c.terms ++ [(coeff, ℓ)]) = _
  rw [signedEval_append]
  simp [signedEval]

/-- **Encode-sum identity.** The signed sum of `encodeLinearLe terms b` is exactly
    `Σ aᵢ·maxVal − Σ aᵢ·intValue` (independent of the bound `b`, which only sets
    the rhs).  This is the equational form of the substitution theorem's `key`. -/
theorem signedEval_encode_eq (v : Valuation S) (terms : List (Int × Fin S.nInt)) (b : Int) :
    signedEval v (encodeLinearLe terms b).terms
      = (terms.map (fun p => p.1 * S.maxVal p.2)).sum
        - (terms.map (fun p => p.1 * v.intValue p.2)).sum := by
  rw [signedEval_encode]
  induction terms with
  | nil => simp
  | cons p rest ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have hp : p.1 * (∑ j : Fin (S.width p.2), S.gap p.2 j * (if v (.thr p.2 j) then (1 : ℤ) else 0))
        = p.1 * S.maxVal p.2 - p.1 * v.intValue p.2 := by
      unfold Valuation.intValue; ring
    rw [hp]; ring

/-- Negating every coefficient negates a `f`-weighted sum (for any `f`). -/
private theorem neg_coeff_map_sum (f : Fin S.nInt → Int) (terms : List (Int × Fin S.nInt)) :
    ((terms.map (fun p => ((-p.1 : Int), p.2))).map (fun p => p.1 * f p.2)).sum
      = -((terms.map (fun p => p.1 * f p.2)).sum) := by
  induction terms with
  | nil => simp
  | cons p t ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-! ### The range bound: `|Σ aᵢ·intValue| ≤ Σ |aᵢ|·maxAbs` -/

/-- `nth` is monotone on in-range indices (the domain is sorted). -/
private theorem nth_le_nth (i : Fin S.nInt) {p q : ℕ} (hpq : p ≤ q)
    (hq : q < (S.values i).length) : S.nth i p ≤ S.nth i q := by
  rcases eq_or_lt_of_le hpq with rfl | hlt
  · exact le_refl _
  · have hp : p < (S.values i).length := lt_trans hlt hq
    show (S.values i).getD p 0 ≤ (S.values i).getD q 0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    exact le_of_lt ((List.pairwise_iff_getElem.mp (S.sorted i)) p q hp hq hlt)

/-- `maxAbs i = max(|minVal i|, |maxVal i|)` — a bound on `|xᵢ|` over the domain. -/
def CSPSig.maxAbs (S : CSPSig) (i : Fin S.nInt) : Int := max |S.nth i 0| |S.maxVal i|

/-- Under order consistency, the recovered value is bounded in magnitude by
    `maxAbs i` (it lies between `minVal i = nth i 0` and `maxVal i`). -/
theorem intValue_abs_le_maxAbs (v : Valuation S) (hv : v.orderConsistent) (i : Fin S.nInt) :
    |v.intValue i| ≤ S.maxAbs i := by
  obtain ⟨m, hmw, hval, _⟩ := intValue_switch i v hv
  have hlen : (S.values i).length = S.width i + 1 := by
    have hne := S.nonempty i
    have hwd : S.width i = (S.values i).length - 1 := rfl
    omega
  have hmlt : m < (S.values i).length := by omega
  have hwlt : S.width i < (S.values i).length := by omega
  have hlo : S.nth i 0 ≤ v.intValue i := by rw [hval]; exact nth_le_nth i (Nat.zero_le m) hmlt
  have hhi : v.intValue i ≤ S.maxVal i := by
    rw [hval, show S.maxVal i = S.nth i (S.width i) from rfl]; exact nth_le_nth i hmw hwlt
  rw [abs_le, CSPSig.maxAbs]
  have h1 := le_abs_self (S.maxVal i)
  have h2 := neg_abs_le (S.nth i 0)
  have h3 := le_max_left |S.nth i 0| |S.maxVal i|
  have h4 := le_max_right |S.nth i 0| |S.maxVal i|
  omega

/-- **Range bound.** Under order consistency, the linear sum is bounded in
    magnitude by `Σ |aᵢ|·maxAbs i`. -/
theorem linear_abs_bound (v : Valuation S) (hv : v.orderConsistent)
    (terms : List (Int × Fin S.nInt)) :
    |(terms.map (fun p => p.1 * v.intValue p.2)).sum|
      ≤ (terms.map (fun p => |p.1| * S.maxAbs p.2)).sum := by
  induction terms with
  | nil => simp
  | cons p t ih =>
    simp only [List.map_cons, List.sum_cons]
    have hterm : |p.1 * v.intValue p.2| ≤ |p.1| * S.maxAbs p.2 := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (intValue_abs_le_maxAbs v hv p.2) (abs_nonneg p.1)
    calc |p.1 * v.intValue p.2 + (t.map (fun p => p.1 * v.intValue p.2)).sum|
        ≤ |p.1 * v.intValue p.2| + |(t.map (fun p => p.1 * v.intValue p.2)).sum| := abs_add_le _ _
      _ ≤ |p.1| * S.maxAbs p.2 + (t.map (fun p => |p.1| * S.maxAbs p.2)).sum := add_le_add hterm ih

/-- The encode-sum identity for a coefficient-negated term list (used by the
    `Σ ≥ b+1` branch): `signedEval = −Σ aᵢ·maxVal + Σ aᵢ·intValue`. -/
private theorem signedEval_encode_neg_eq (v : Valuation S)
    (terms : List (Int × Fin S.nInt)) (b : Int) :
    signedEval v (encodeLinearLe (terms.map (fun p => ((-p.1 : Int), p.2))) b).terms
      = -((terms.map (fun p => p.1 * S.maxVal p.2)).sum)
        + (terms.map (fun p => p.1 * v.intValue p.2)).sum := by
  rw [signedEval_encode_eq, neg_coeff_map_sum S.maxVal, neg_coeff_map_sum (fun i => v.intValue i)]
  ring

/-! ### The Big-M disequality encoder -/

/-- The Big-M constant for `Σ aᵢ·xᵢ ≠ b`: dominates `|Σ aᵢ·xᵢ − b|` over all
    in-domain assignments. -/
def bigM (terms : List (Int × Fin S.nInt)) (b : Int) : Int :=
  (terms.map (fun p => |p.1| * S.maxAbs p.2)).sum + |b| + 1

/-- Encode `Σ aᵢ·xᵢ ≠ b` with the fresh `aux` selector `s`, as two Big-M
    constraints (`s=false ⇒ Σ ≤ b−1`, `s=true ⇒ Σ ≥ b+1`).  Each is a reused
    linear encoding with one appended selector term. -/
def encodeLinearNe (terms : List (Int × Fin S.nInt)) (b : Int) (s : Fin S.nAux) :
    List (SignedPBConstr (PBVar S)) :=
  let M := bigM terms b
  [ (encodeLinearLe terms (b - 1)).addTerm M (.pos (.aux s)),
    (encodeLinearLe (terms.map (fun p => ((-p.1 : Int), p.2))) (M - b - 1)).addTerm (-M)
      (.pos (.aux s)) ]

/-- **Soundness.** If the linear sum differs from `b` and the selector `s` is set
    to `decide(Σ > b)`, both Big-M constraints hold.  The selected branch holds
    exactly; the unselected one is vacuous because `M` dominates the range
    (`linear_abs_bound`). -/
theorem encodeLinearNe_sound (v : Valuation S) (hv : v.orderConsistent)
    (terms : List (Int × Fin S.nInt)) (b : Int) (s : Fin S.nAux)
    (hne : (terms.map (fun p => p.1 * v.intValue p.2)).sum ≠ b)
    (hs : v (.aux s) = decide ((terms.map (fun p => p.1 * v.intValue p.2)).sum > b)) :
    ∀ c ∈ encodeLinearNe terms b s, c.sat v := by
  -- Abbreviations and the key numeric facts (the range bound + `b ≤ |b|`, `−b ≤ |b|`).
  have hbound := linear_abs_bound v hv terms
  rw [abs_le] at hbound
  obtain ⟨hBlo, hBhi⟩ := hbound
  have hbabs : b ≤ |b| := le_abs_self b
  have hbabs' : -b ≤ |b| := neg_le_abs b
  -- The selector literal's integer value.
  have hsint : (evalLit v (.pos (.aux s)) : Int)
      = if (terms.map (fun p => p.1 * v.intValue p.2)).sum > b then 1 else 0 := by
    simp only [evalLit, hs]
    by_cases h : (terms.map (fun p => p.1 * v.intValue p.2)).sum > b <;> simp [h]
  intro c hc
  simp only [encodeLinearNe, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · -- C1: Σ ≤ (b−1) + M·⟦s⟧.
    show signedEval v _ ≥ (encodeLinearLe terms (b - 1)).rhs
    rw [signedEval_addTerm, signedEval_encode_eq, hsint]
    simp only [encodeLinearLe, bigM]
    by_cases h : (terms.map (fun p => p.1 * v.intValue p.2)).sum > b
    · rw [if_pos h, mul_one]; omega
    · rw [if_neg h, mul_zero]; omega
  · -- C2: Σ ≥ (b+1) − M·(1−⟦s⟧).
    show signedEval v _ ≥ (encodeLinearLe (terms.map (fun p => ((-p.1 : Int), p.2)))
      (bigM terms b - b - 1)).rhs
    rw [signedEval_addTerm, signedEval_encode_neg_eq, hsint]
    simp only [encodeLinearLe]
    rw [neg_coeff_map_sum S.maxVal]
    simp only [bigM]
    by_cases h : (terms.map (fun p => p.1 * v.intValue p.2)).sum > b
    · rw [if_pos h, mul_one]; omega
    · rw [if_neg h, mul_zero]; omega

/-! ### The `extend`-bridge: feeding the selector from a solution -/

/-- **Bridge.** A normalized `encodeLinearNe` constraint is modelled by
    `extend a bA auxA` whenever the linear sum on `a` differs from `b` and the
    selector aux `auxA s` is set to `decide(Σ aᵢ·a(xᵢ) > b)`.  This is the
    per-constraint soundness fact the generic spine consumes, with the aux-setter
    `auxOf a := s ↦ decide(Σ aᵢ·a(xᵢ) > b)`.  Composes `encodeLinearNe_sound`
    with `extend_intValue` / `extend_orderConsistent` / `extend_aux`. -/
theorem extend_sat_encodeLinearNe (a : Fin S.nInt → Int) (bA : Fin S.nBool → Bool)
    (auxA : Fin S.nAux → Bool) (hdom : ∀ i, a i ∈ S.values i)
    (terms : List (Int × Fin S.nInt)) (b : Int) (s : Fin S.nAux)
    (hne : (terms.map (fun p => p.1 * a p.2)).sum ≠ b)
    (hauxs : auxA s = decide ((terms.map (fun p => p.1 * a p.2)).sum > b))
    (c' : PBConstr (PBVar S))
    (hc : c' ∈ (encodeLinearNe terms b s).filterMap normalize) :
    c'.sat (extend a bA auxA) := by
  rw [List.mem_filterMap] at hc
  obtain ⟨sc, hsc_mem, hnorm⟩ := hc
  rw [← normalize_sat_iff _ _ hnorm]
  have hsum : (terms.map (fun p => p.1 * (extend a bA auxA).intValue p.2)).sum
            = (terms.map (fun p => p.1 * a p.2)).sum :=
    congrArg List.sum (List.map_congr_left (fun p _ => by rw [extend_intValue a bA auxA hdom p.2]))
  refine encodeLinearNe_sound (extend a bA auxA) (extend_orderConsistent a bA auxA)
    terms b s ?_ ?_ sc hsc_mem
  · rw [hsum]; exact hne
  · rw [extend_aux, hauxs, hsum]

/-! ### Unit test: `x ∈ {0,1,2}` with `x ≠ 1` via the Big-M selector

A single integer variable over `{0,1,2}` and one selector aux.  Under the
all-false threshold valuation the recovered value is the domain maximum
`x₀ = 2` (no "`x ≤ k`" threshold is set), so the selector `s = decide(2 > 1)`
must be `true`; both Big-M constraints then hold.
-/

namespace LinearNeTest

/-- One integer variable over `{0,1,2}`, one selector aux, no Booleans. -/
def sigNe : CSPSig where
  nInt := 1
  nBool := 0
  nAux := 1
  values := fun _ => [0, 1, 2]
  sorted := by intro _; decide
  nonempty := by intro _; decide

/-- Valuation with all thresholds false (so `x₀ = maxVal = 2`) and selector
    `true` (matching `decide(2 > 1)`). -/
def vNe : Valuation sigNe
  | .aux _ => true
  | _      => false

theorem vNe_orderConsistent : vNe.orderConsistent := by
  intro i j j' hj' hj; exact absurd hj (by simp [vNe])

-- `x₀ = 2`, recovered from the all-false threshold valuation (top of the domain).
example : vNe.intValue ⟨0, by decide⟩ = 2 := by decide

-- The Big-M `≠ 1` encoding is satisfied by `vNe` (sum `2 ≠ 1`; selector `true`).
example : ∀ c ∈ encodeLinearNe [((1 : Int), (⟨0, by decide⟩ : Fin sigNe.nInt))] 1 ⟨0, by decide⟩,
    c.sat vNe :=
  encodeLinearNe_sound vNe vNe_orderConsistent _ 1 ⟨0, by decide⟩ (by decide) (by decide)

end LinearNeTest

end CSP.L2S.PB
