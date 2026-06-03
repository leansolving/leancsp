import CSP.L2S.Backends.PB.BoolGates

namespace CSP.L2S.PB

/-!
# PB backend — recursive Tseitin compiler for Boolean expressions (PLAN §6.7)

Layered on the literal-level gates (`BoolGates.lean`): a recursive `BoolExpr α`
inductive and a `compile` that emits the Tseitin clause set for a whole formula,
reusing one fresh output variable per subformula.

**Aux allocation.** Rather than a `StateM Nat` fresh-name counter (which forces an
awkward `Fin S.nAux` bound during compilation), we index each gate's output
variable by the *subformula it computes*: the variable type is `α ⊕ BoolExpr α`,
an input `Sum.inl a` or a gate output `Sum.inr e`.  Two consequences:

* identical subformulas share one output variable (structural common-subexpression
  elimination, for free);
* the **canonical valuation** `vCanon bA (Sum.inr e) := e.eval bA` makes
  "output bit = formula value" hold *definitionally*, so soundness is a clean
  induction that simply discharges each gate's bit relation via the corresponding
  `gate*_sound` lemma.

`compile_sound` proves every emitted clause is satisfied by `vCanon bA` — i.e. the
encoding is faithful: any model of `bA` extends (canonically) to a model of the
clause set.  The map `α ⊕ BoolExpr α → PBVar S` and the `extend`-bridge into the
generic spine are a separate concern (no pure-Boolean corpus consumer exists yet).
-/

variable {α : Type}

/-- A Boolean expression over input variables `α`. -/
inductive BoolExpr (α : Type) where
  | var (a : α)
  | tt
  | ff
  | not (e : BoolExpr α)
  | and (e₁ e₂ : BoolExpr α)
  | or (e₁ e₂ : BoolExpr α)
  | iff (e₁ e₂ : BoolExpr α)

/-- The Boolean value of an expression under an input assignment. -/
def BoolExpr.eval (bA : α → Bool) : BoolExpr α → Bool
  | .var a => bA a
  | .tt => true
  | .ff => false
  | .not e => !(e.eval bA)
  | .and e₁ e₂ => e₁.eval bA && e₂.eval bA
  | .or e₁ e₂ => e₁.eval bA || e₂.eval bA
  | .iff e₁ e₂ => e₁.eval bA == e₂.eval bA

/-- The Tseitin variable type: an input `Sum.inl a` or a per-subformula output
    `Sum.inr e`. -/
abbrev TVar (α : Type) := α ⊕ BoolExpr α

/-- The output literal of a subformula: the input literal itself for `var`,
    otherwise the (positive) per-subformula output variable. -/
def BoolExpr.outLit : BoolExpr α → Lit (TVar α)
  | .var a => Lit.pos (Sum.inl a)
  | e       => Lit.pos (Sum.inr e)

/-- The Tseitin clause set for an expression: one gate per connective, constraining
    that subformula's output variable to the connective of its children's outputs;
    constants are pinned by a unit clause. -/
def BoolExpr.compile : BoolExpr α → List (SignedPBConstr (TVar α))
  | .var _ => []
  | .tt => [clause [BoolExpr.tt.outLit]]
  | .ff => [clause [BoolExpr.ff.outLit.negate]]
  | .not e => gateNot (BoolExpr.not e).outLit e.outLit ++ e.compile
  | .and e₁ e₂ =>
      gateAnd (BoolExpr.and e₁ e₂).outLit e₁.outLit e₂.outLit ++ e₁.compile ++ e₂.compile
  | .or e₁ e₂ =>
      gateOr (BoolExpr.or e₁ e₂).outLit e₁.outLit e₂.outLit ++ e₁.compile ++ e₂.compile
  | .iff e₁ e₂ =>
      gateIff (BoolExpr.iff e₁ e₂).outLit e₁.outLit e₂.outLit ++ e₁.compile ++ e₂.compile

/-- The canonical valuation: inputs follow `bA`, each output variable takes the value
    of the subformula it represents. -/
def vCanon (bA : α → Bool) : TVar α → Bool
  | .inl a => bA a
  | .inr e => e.eval bA

/-- A bit (`0`/`1` as `Nat`) for a Boolean (private proof helper). -/
private def bit (b : Bool) : Nat := if b then 1 else 0

private theorem bit_not (b : Bool) : bit (!b) = 1 - bit b := by cases b <;> rfl
private theorem bit_and (a b : Bool) : bit (a && b) = min (bit a) (bit b) := by
  cases a <;> cases b <;> rfl
private theorem bit_or (a b : Bool) : bit (a || b) = max (bit a) (bit b) := by
  cases a <;> cases b <;> rfl
private theorem bit_iff (a b : Bool) :
    bit (a == b) = 1 - (max (bit a) (bit b) - min (bit a) (bit b)) := by
  cases a <;> cases b <;> rfl

/-- Under the canonical valuation, a subformula's output literal evaluates to its
    Boolean value — definitionally, by the `Sum.inr e ↦ e.eval` clause of `vCanon`. -/
private theorem evalLit_outLit (bA : α → Bool) (e : BoolExpr α) :
    evalLit (vCanon bA) e.outLit = bit (e.eval bA) := by
  cases e <;> rfl

/-- **Soundness.** Every clause emitted by `compile e` is satisfied by the canonical
    valuation `vCanon bA`.  Proved by induction on `e`, discharging each gate's bit
    relation with the matching `gate*_sound` and `evalLit_outLit`. -/
theorem compile_sound (bA : α → Bool) (e : BoolExpr α) :
    ∀ c ∈ e.compile, c.sat (vCanon bA) := by
  induction e with
  | var a => intro c hc; simp only [BoolExpr.compile, List.not_mem_nil] at hc
  | tt =>
      intro c hc
      simp only [BoolExpr.compile, List.mem_singleton] at hc; subst hc
      rw [clause_sat_eq]
      simp [BoolExpr.outLit, evalLit, vCanon, BoolExpr.eval]
  | ff =>
      intro c hc
      simp only [BoolExpr.compile, List.mem_singleton] at hc; subst hc
      rw [clause_sat_eq]
      simp [BoolExpr.outLit, Lit.negate, evalLit, vCanon, BoolExpr.eval]
  | not e ih =>
      intro c hc
      simp only [BoolExpr.compile, List.mem_append] at hc
      rcases hc with h | h
      · refine gateNot_sound (vCanon bA) (BoolExpr.not e).outLit e.outLit ?_ c h
        rw [evalLit_outLit, evalLit_outLit]; simp only [BoolExpr.eval, bit_not]
      · exact ih c h
  | and e₁ e₂ ih₁ ih₂ =>
      intro c hc
      simp only [BoolExpr.compile, List.mem_append] at hc
      rcases hc with (h | h) | h
      · refine gateAnd_sound (vCanon bA) (BoolExpr.and e₁ e₂).outLit e₁.outLit e₂.outLit ?_ c h
        rw [evalLit_outLit, evalLit_outLit, evalLit_outLit]; simp only [BoolExpr.eval, bit_and]
      · exact ih₁ c h
      · exact ih₂ c h
  | or e₁ e₂ ih₁ ih₂ =>
      intro c hc
      simp only [BoolExpr.compile, List.mem_append] at hc
      rcases hc with (h | h) | h
      · refine gateOr_sound (vCanon bA) (BoolExpr.or e₁ e₂).outLit e₁.outLit e₂.outLit ?_ c h
        rw [evalLit_outLit, evalLit_outLit, evalLit_outLit]; simp only [BoolExpr.eval, bit_or]
      · exact ih₁ c h
      · exact ih₂ c h
  | iff e₁ e₂ ih₁ ih₂ =>
      intro c hc
      simp only [BoolExpr.compile, List.mem_append] at hc
      rcases hc with (h | h) | h
      · refine gateIff_sound (vCanon bA) (BoolExpr.iff e₁ e₂).outLit e₁.outLit e₂.outLit ?_ c h
        rw [evalLit_outLit, evalLit_outLit, evalLit_outLit]
        simp only [BoolExpr.eval]; rw [bit_iff]
      · exact ih₁ c h
      · exact ih₂ c h

/-! ### Unit test: a small formula over two inputs -/

namespace BoolExprCompilerTest

/-- `x₀ ∧ ¬x₁` over two propositional inputs. -/
def ex : BoolExpr (Fin 2) := .and (.var 0) (.not (.var 1))

-- The canonical valuation satisfies every clause of the compiled formula.
example (bA : Fin 2 → Bool) : ∀ c ∈ ex.compile, c.sat (vCanon bA) := compile_sound bA ex

-- The output variable carries the formula's value (`x₀=1, x₁=0 ⊢ x₀ ∧ ¬x₁ = 1`).
example : evalLit (vCanon (fun i : Fin 2 => i == 0)) ex.outLit = 1 := by decide

end BoolExprCompilerTest

end CSP.L2S.PB
