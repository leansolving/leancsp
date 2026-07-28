import CSP.Core
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Vector.Basic

namespace CSP.L2S

/-!
# L2S core

A single `IntCSP` type that is both proof-ready and directly translatable to a
solver.  All variables range over `ℤ`; each constraint carries a semantic pattern
(its meaning, via `patternHolds`) alongside an executable checker.
-/

/-! ### Type Aliases and Foundations -/

/-- Integer domain for all variables -/
abbrev IntDomain := ℤ

/-- Variable indices are finite -/
abbrev VarType (n : ℕ) := Fin n

/-- DecidableEq instance for variable indices -/
instance {n : ℕ} : DecidableEq (VarType n) := inferInstance

/-- Abbreviation for homogeneous constraints -/
abbrev IntDynConstraint (n : ℕ) :=
  DynamicConstraint (VarType n) (fun _ => IntDomain)

/-- Abbreviation for homogeneous assignments -/
abbrev IntAssignment (n : ℕ) :=
  VarType n → IntDomain

/-! ### Relational Operators (for sum and other constraints) -/

/-- Relational operators for constraints -/
inductive RelOp where
  | EQ  -- Equal
  | NE  -- Not equal
  | LT  -- Less than
  | LE  -- Less than or equal
  | GT  -- Greater than
  | GE  -- Greater than or equal
  deriving Repr, DecidableEq

/-! ### Constraint Patterns (Semantic Representation) -/

/--
Semantic patterns for constraint types. These enable MiniZinc translation
by capturing the high-level structure of constraints.
-/
inductive IntConstraint (num_vars : ℕ)
  -- Global constraints
  | alldifferent (vars : List ℕ)
  | alldifferentOffset (vars : List ℕ) (offsets : List ℤ)  -- For diagonal constraints
  | increasing (vars : List ℕ)  -- Variables in non-decreasing order

  -- Arithmetic constraints
  | sum (vars : List ℕ) (op : RelOp) (target : ℤ)
  | linear (vars : List ℕ) (coeffs : List ℤ) (op : RelOp) (target : ℤ)  -- Weighted sum with coefficients
  | count (vars : List ℕ) (value : ℤ) (n : ℕ)
  | count_var (vars : List ℕ) (value : ℤ) (count_var : ℕ)  -- Count with variable result (for magic sequence)
  | element (index : ℕ) (array : List ℤ) (result : ℕ)
  | maximum (vars : List ℕ) (maxVar : ℕ)
  | minimum (vars : List ℕ) (minVar : ℕ)

  -- Bound constraints (for variable domain specification)
  | bound (var : ℕ) (lb ub : ℤ)

  -- Binary comparison constraints
  | eq (var1 var2 : ℕ)  -- var1 = var2
  | ne (var1 var2 : ℕ)  -- var1 ≠ var2
  | lt (var1 var2 : ℕ)  -- var1 < var2
  | le (var1 var2 : ℕ)  -- var1 ≤ var2
  | gt (var1 var2 : ℕ)  -- var1 > var2
  | ge (var1 var2 : ℕ)  -- var1 ≥ var2

  -- Unary comparison constraints (variable to constant)
  | eq_const (var : ℕ) (value : ℤ)  -- var = value
  | ne_const (var : ℕ) (value : ℤ)  -- var ≠ value
  | lt_const (var : ℕ) (value : ℤ)  -- var < value
  | le_const (var : ℕ) (value : ℤ)  -- var ≤ value
  | gt_const (var : ℕ) (value : ℤ)  -- var > value
  | ge_const (var : ℕ) (value : ℤ)  -- var ≥ value

  -- Logical/Disjunctive constraints
  | schur_triple (var1 var2 var3 : ℕ)  -- Not all three variables equal: x ≠ y ∨ x ≠ z ∨ y ≠ z

  -- Absolute value constraints
  | abs_diff_rel (var1 var2 : ℕ) (op : RelOp) (target : ℤ)  -- |var1 - var2| op target
  | abs_diff_var (var1 var2 result : ℕ)  -- result = |var1 - var2|

  -- Modulo constraints
  | modulo (var : ℕ) (n k : ℤ)  -- var mod n = k

  -- Sliding window constraints
  | sliding_sum (vars : List ℕ) (window_size : ℕ) (op : RelOp) (target : ℤ)  -- For each window of size k, sum op target

  -- Boolean gate constraints (for 0/1 valued variables)
  | not_gate (in1 out : ℕ)      -- out = ¬in (unary negation)
  | and_gate (in1 in2 out : ℕ)  -- out = in1 ∧ in2
  | or_gate (in1 in2 out : ℕ)   -- out = in1 ∨ in2
  | xor_gate (in1 in2 out : ℕ)  -- out = in1 ⊕ in2
  | nand_gate (in1 in2 out : ℕ) -- out = ¬(in1 ∧ in2)
  | nor_gate (in1 in2 out : ℕ)  -- out = ¬(in1 ∨ in2)

  -- Multi-input logical operations
  | and_all (vars : List ℕ) (result : ℕ)  -- result = ∧ vars
  | or_all (vars : List ℕ) (result : ℕ)   -- result = ∨ vars
  | xor_all (vars : List ℕ) (result : ℕ)  -- result = ⊕ vars (parity)

  -- Implication and equivalence
  | implies (premise conclusion : ℕ)  -- premise ⇒ conclusion
  | iff (var1 var2 : ℕ)               -- var1 ↔ var2
  | if_then (var : ℕ) (value : ℤ) (next_var : ℕ) (next_value : ℤ)  -- if var=value then next_var=next_value
  | if_then_or (var : ℕ) (value : ℤ) (next_var : ℕ) (allowed_values : List ℤ)  -- if var=value then next_var ∈ allowed_values

  -- Cardinality constraints (for Boolean variables)
  | at_least_k (vars : List ℕ) (k : ℕ)  -- sum(vars) ≥ k
  | at_most_k (vars : List ℕ) (k : ℕ)   -- sum(vars) ≤ k
  | exactly_k (vars : List ℕ) (k : ℕ)   -- sum(vars) = k

  -- Arithmetic constraints with variable targets (not constants)
  | sum_rel_var (vars : List ℕ) (op : RelOp) (target_var : ℕ)  -- sum(vars) op target_var
  | linear_rel_var (vars : List ℕ) (coeffs : List ℤ) (op : RelOp) (target_var : ℕ)  -- Σ(coeffs[i]*vars[i]) op target_var
  | product_rel_var (vars : List ℕ) (op : RelOp) (target_var : ℕ)  -- product(vars) op target_var

  -- Value precedence (Law–Lee 2004): a colour `v ∈ [1, colors)` may first appear,
  -- scanning `x_0, x_1, …`, only after `v-1` has.  Sound for any CSP closed under all
  -- permutations of the colour values (see `CSP/L2S/ValuePrecedence.lean`).
  | value_precedence (colors : ℕ)

  -- Strict lexicographic reversal leader `x <_lex rev(x)`, for the index reversal
  -- `i ↦ (num_vars-1)-i`.  A whole-CSP constraint.  Sound ONLY when that reversal is a
  -- symmetry of the CSP; see `Proofs/SchurReversalCounterexample.lean`.
  | strictLexRevLeader

  -- Scheduling constraints
  | disjunctive (tasks : List ℕ) (durations : List ℤ)  -- Tasks on unary resource must not overlap

  -- Unknown pattern (fallback)
  | unknown (arity : ℕ) (scope : List ℕ)
  deriving Repr, DecidableEq

/-! ### Pattern Semantics (meaning of a constraint from its `pattern`) -/

/-- Value of pattern variable `v` (a raw `ℕ` index) under assignment `a`;
    out-of-range indices default to `0` (they do not occur in well-formed CSPs). -/
def valAt {n : ℕ} (a : IntAssignment n) (v : ℕ) : ℤ :=
  if h : v < n then a ⟨v, h⟩ else 0

/-- Interpret a `RelOp` as a relation on `ℤ`. -/
def relHolds : RelOp → ℤ → ℤ → Prop
  | .EQ, x, y => x = y
  | .NE, x, y => x ≠ y
  | .LT, x, y => x < y
  | .LE, x, y => x ≤ y
  | .GT, x, y => x > y
  | .GE, x, y => x ≥ y

/-- The meaning of a constraint pattern as a predicate on assignments.
    `satisfiesConstraintInt` is defined through this, making a constraint's meaning a
    function of its finite `pattern` rather than its opaque `dynamic` field. -/
def patternHolds {n : ℕ} : IntConstraint n → IntAssignment n → Prop
  | .alldifferent vars, a => (vars.map (valAt a)).Nodup
  | .alldifferentOffset vars offsets, a =>
      ((vars.zip offsets).map (fun p => valAt a p.1 + p.2)).Nodup
  | .increasing vars, a => List.Pairwise (· ≤ ·) (vars.map (valAt a))
  | .sum vars op target, a => relHolds op (vars.map (valAt a)).sum target
  | .linear vars coeffs op target, a =>
      relHolds op (List.zipWith (· * ·) coeffs (vars.map (valAt a))).sum target
  | .count vars value target, a =>
      ((vars.map (valAt a)).filter (· = value)).length = target
  | .count_var vars value cvar, a =>
      (((vars.map (valAt a)).filter (· = value)).length : ℤ) = valAt a cvar
  | .element idx array result, a =>
      valAt a idx ≥ 1 ∧ (array[(valAt a idx).natAbs - 1]?).any (· = valAt a result)
  | .maximum vars mx, a =>
      (vars.map (valAt a)).all (· ≤ valAt a mx) ∧ (vars.map (valAt a)).any (· = valAt a mx)
  | .minimum vars mn, a =>
      (vars.map (valAt a)).all (valAt a mn ≤ ·) ∧ (vars.map (valAt a)).any (· = valAt a mn)
  | .bound v lb ub, a => lb ≤ valAt a v ∧ valAt a v ≤ ub
  | .eq v1 v2, a => valAt a v1 = valAt a v2
  | .ne v1 v2, a => valAt a v1 ≠ valAt a v2
  | .lt v1 v2, a => valAt a v1 < valAt a v2
  | .le v1 v2, a => valAt a v1 ≤ valAt a v2
  | .gt v1 v2, a => valAt a v1 > valAt a v2
  | .ge v1 v2, a => valAt a v1 ≥ valAt a v2
  | .eq_const v c, a => valAt a v = c
  | .ne_const v c, a => valAt a v ≠ c
  | .lt_const v c, a => valAt a v < c
  | .le_const v c, a => valAt a v ≤ c
  | .gt_const v c, a => valAt a v > c
  | .ge_const v c, a => valAt a v ≥ c
  | .schur_triple v1 v2 v3, a =>
      valAt a v1 ≠ valAt a v2 ∨ valAt a v1 ≠ valAt a v3 ∨ valAt a v2 ≠ valAt a v3
  | .abs_diff_rel v1 v2 op target, a =>
      relHolds op ((valAt a v1 - valAt a v2).natAbs : ℤ) target
  | .abs_diff_var v1 v2 result, a => valAt a result = ((valAt a v1 - valAt a v2).natAbs : ℤ)
  | .modulo v k m, a => valAt a v % k = m
  | .sliding_sum vars w op target, a =>
      ∀ s ∈ List.range (vars.length - w + 1),
        relHolds op (((vars.map (valAt a)).drop s).take w).sum target
  | .not_gate i o, a => valAt a o = 1 - valAt a i
  | .and_gate i1 i2 o, a => valAt a o = min (valAt a i1) (valAt a i2)
  | .or_gate i1 i2 o, a => valAt a o = max (valAt a i1) (valAt a i2)
  | .xor_gate i1 i2 o, a => (valAt a i1 + valAt a i2) % 2 = valAt a o
  | .nand_gate i1 i2 o, a =>
      valAt a o ≥ 1 - valAt a i1 ∧ valAt a o ≥ 1 - valAt a i2 ∧
        valAt a o ≤ 2 - valAt a i1 - valAt a i2
  | .nor_gate i1 i2 o, a =>
      valAt a o ≤ 1 - valAt a i1 ∧ valAt a o ≤ 1 - valAt a i2 ∧
        valAt a o ≥ 1 - valAt a i1 - valAt a i2
  | .and_all vars result, a =>
      (vars.map (valAt a)) ≠ [] ∧
      valAt a result = (vars.map (valAt a)).foldl (fun acc x => if x < acc then x else acc)
        (vars.map (valAt a)).headI
  | .or_all vars result, a =>
      (vars.map (valAt a)) ≠ [] ∧
      valAt a result = (vars.map (valAt a)).foldl (fun acc x => if x > acc then x else acc)
        (vars.map (valAt a)).headI
  | .xor_all vars result, a => (vars.map (valAt a)).sum % 2 = valAt a result
  | .implies p q, a => valAt a q ≥ valAt a p
  | .iff v1 v2, a => valAt a v1 = valAt a v2
  | .if_then v value nv nvalue, a => valAt a v ≠ value ∨ valAt a nv = nvalue
  | .if_then_or v value nv allowed, a => valAt a v ≠ value ∨ (valAt a nv) ∈ allowed
  | .at_least_k vars k, a => (vars.map (valAt a)).sum ≥ (k : ℤ)
  | .at_most_k vars k, a => (vars.map (valAt a)).sum ≤ (k : ℤ)
  | .exactly_k vars k, a => (vars.map (valAt a)).sum = (k : ℤ)
  | .sum_rel_var vars op tvar, a => relHolds op (vars.map (valAt a)).sum (valAt a tvar)
  | .linear_rel_var vars coeffs op tvar, a =>
      relHolds op (List.zipWith (· * ·) coeffs (vars.map (valAt a))).sum (valAt a tvar)
  | .product_rel_var vars op tvar, a =>
      relHolds op ((vars.map (valAt a)).foldl (· * ·) 1) (valAt a tvar)
  | .value_precedence _colors, a =>
      ∀ j : Fin n, 1 ≤ a j → ∃ i : Fin n, i.val < j.val ∧ a i = a j - 1
  | .strictLexRevLeader, a =>
      -- `x <_lex rev(x)`: at the first index `p` where `x` and its reversal differ,
      -- `x` is strictly smaller.
      ∃ p : Fin n, (∀ q : Fin n, q < p → a q = a (Fin.rev q)) ∧ a p < a (Fin.rev p)
  | .disjunctive _ _, _ => True   -- scheduling: not used by the PB pipeline
  | .unknown _ _, _ => True       -- fallback: no semantics

/-- `relHolds op` is decidable on `ℤ`. -/
instance (op : RelOp) (x y : ℤ) : Decidable (relHolds op x y) := by
  cases op <;> unfold relHolds <;> infer_instance

/-- A constraint pattern's meaning is decidable (a finite check over the assignment). -/
instance instDecidablePatternHolds {n : ℕ} (c : IntConstraint n) (a : IntAssignment n) :
    Decidable (patternHolds c a) := by
  cases c <;> unfold patternHolds <;> infer_instance

/-- Map an `IntConstraint` (one of the finite, available constraints) to its *real*
    underlying general `DynamicConstraint`: the full-variable scope with the decidable
    `patternHolds` check.  This keeps the general CSP framework while the front-end is a
    finite inductive. -/
def toDynamic {n : ℕ} (c : IntConstraint n) : IntDynConstraint n :=
  DynamicConstraint.mk n
    { scope := _root_.Vector.ofFn id
      check := fun vals => decide (patternHolds c (fun i => vals i)) }

/-! ### Unified IntCSP Structure -/

/-- An integer CSP: a variable count plus a list of `IntConstraint`s.  A constraint's
    meaning is given by `patternHolds`; `toDynamic` (see `Embedding`) maps it to the
    underlying general `DynamicConstraint`, keeping the general framework while the
    front-end stays a finite inductive. -/
structure IntCSP where
  /-- Number of variables in the CSP -/
  num_vars : ℕ
  /-- List of constraints (each one of the finite available `IntConstraint`s) -/
  constraints : List (IntConstraint num_vars)

namespace IntCSP

/-! ### Solution Checking -/

/-- A constraint is satisfied by an assignment iff its pattern's meaning holds
    (`patternHolds`).  Equivalent to satisfying its real underlying general constraint
    `toDynamic c` (see `Embedding.satisfiesConstraintInt_iff_toDynamic`). -/
def satisfiesConstraintInt (c : IntConstraint n) (assignment : IntAssignment n) : Prop :=
  patternHolds c assignment

/-- Satisfaction is exactly satisfaction of the real underlying general constraint. -/
theorem satisfiesConstraintInt_iff_toDynamic {n : ℕ} (c : IntConstraint n)
    (a : IntAssignment n) :
    satisfiesConstraintInt c a ↔ satisfies_dynamic_constraint (toDynamic c) a := by
  have hfun : (fun i => a ((_root_.Vector.ofFn (id : Fin n → Fin n)).get i)) = a := by
    funext i; congr 1; simp [_root_.Vector.get]
  unfold satisfiesConstraintInt toDynamic satisfies_dynamic_constraint satisfies_constraint
  simp only [CSP.sat, map_assignment, hfun, decide_eq_true_eq]

/-- Check if an assignment is a solution to the CSP -/
def isSolutionInt (csp : IntCSP) (assignment : IntAssignment csp.num_vars) : Prop :=
  ∀ c ∈ csp.constraints, satisfiesConstraintInt c assignment

/-- Check if a CSP is satisfiable (has at least one solution) -/
def isSatisfiableInt (csp : IntCSP) : Prop :=
  ∃ assignment, isSolutionInt csp assignment

/-! ### Bound Extraction (for MiniZinc Variable Declarations) -/

/-- Extract bounds for a variable from bound constraint patterns -/
def extractVariableBounds (csp : IntCSP)
    (var : VarType csp.num_vars) : ℤ × ℤ :=
  -- Scan through constraints looking for bound patterns for this variable
  let bounds := csp.constraints.filterMap fun tc =>
    match tc with
    | IntConstraint.bound v lb ub => if v = var.val then some (lb, ub) else none
    | _ => none

  -- If we found bounds, use them; otherwise default to reasonable range
  match bounds with
  | [] => (-1000, 1000)  -- Default range for unbounded variables
  | (lb, ub) :: _ => (lb, ub)  -- Use first bound found

/-- Extract bounds for all variables -/
def extractAllBounds (csp : IntCSP) :
    VarType csp.num_vars → (ℤ × ℤ) :=
  fun var => extractVariableBounds csp var

/-! ### The `bound`-prefix shape -/

/-!
A CSP shaped `⟨n, (List.range n).map (fun x => bound x (lo x) (hi x)) ++ rest⟩` reads its
own bounds back, satisfying the `hbound` side-goal of `CSP.L2S.PB.csp_unsat` for every `n`
at once.

Pass `hbound_of_range_prefix` rather than letting `csp_unsat`'s `by decide` default
re-derive it per instance: deciding it makes the elaborator reduce the generator
symbolically, costing minutes and gigabytes on large instances.  CSPs given as literal
data decide cheaply and need neither.
-/

/-- `List.range n` hits `i < n` exactly once, so a single-point `filterMap` over it is a singleton. -/
theorem filterMap_range_single {α : Type} (n i : ℕ) (hi : i < n) (g : ℕ → α) :
    (List.range n).filterMap (fun x => if x = i then some (g x) else none) = [g i] := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.filterMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [ih h]; simp [Nat.ne_of_gt h]
    · subst h
      have : ∀ x ∈ List.range i, (if x = i then some (g x) else none) = none := by
        intro x hx; simp [Nat.ne_of_lt (List.mem_range.mp hx)]
      rw [List.filterMap_eq_nil_iff.mpr this]; simp

/-- A `bound`-prefixed CSP reads its own bounds back: the prefix supplies the first (hence chosen)
    match for every variable, whatever `rest` contains. -/
theorem extractVariableBounds_of_range_prefix {n : ℕ} (lo hi : ℕ → ℤ)
    (rest : List (IntConstraint n)) (i : Fin n) :
    (IntCSP.mk n ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
        ++ rest)).extractVariableBounds i = (lo i.val, hi i.val) := by
  show (match ((((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
          ++ rest)).filterMap _) with
        | [] => ((-1000 : ℤ), (1000 : ℤ)) | (lb, ub) :: _ => (lb, ub)) = _
  rw [List.filterMap_append, List.filterMap_map, Function.comp_def]
  rw [filterMap_range_single n i.val i.isLt (fun x => (lo x, hi x))]
  rfl

/-- `csp_unsat`'s `hbound`, once and for all `n`, for any `bound`-prefixed CSP. -/
theorem hbound_of_range_prefix {n : ℕ} (lo hi : ℕ → ℤ) (rest : List (IntConstraint n)) :
    ∀ i : Fin (IntCSP.mk n ((List.range n).map
        (fun x => IntConstraint.bound x (lo x) (hi x)) ++ rest)).num_vars,
      IntConstraint.bound i.val
          ((IntCSP.mk n ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ rest)).extractVariableBounds i).1
          ((IntCSP.mk n ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ rest)).extractVariableBounds i).2
        ∈ (IntCSP.mk n ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
            ++ rest)).constraints := by
  intro i
  rw [extractVariableBounds_of_range_prefix]
  exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr i.isLt))

/-- `c` is not a `bound` constraint.  Only the head constructor is inspected, so `trivial` settles
    it for any concrete constraint without touching its payload. -/
def NotBound {n : ℕ} (c : IntConstraint n) : Prop :=
  match c with | IntConstraint.bound _ _ _ => False | _ => True

/-- Same, for a generator ending `bounds ++ r₁ ++ r₂`. `++` is `infixl`, so that parses as
    `(bounds ++ r₁) ++ r₂`, whose head is an append rather than the `map`. -/
theorem hbound_of_range_prefix₂ {n : ℕ} (lo hi : ℕ → ℤ) (r₁ r₂ : List (IntConstraint n)) :
    ∀ i : Fin (IntCSP.mk n ((List.range n).map
        (fun x => IntConstraint.bound x (lo x) (hi x)) ++ r₁ ++ r₂)).num_vars,
      IntConstraint.bound i.val
          ((IntCSP.mk n ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ r₁ ++ r₂)).extractVariableBounds i).1
          ((IntCSP.mk n ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ r₁ ++ r₂)).extractVariableBounds i).2
        ∈ (IntCSP.mk n ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
            ++ r₁ ++ r₂)).constraints := by
  rw [List.append_assoc]
  exact hbound_of_range_prefix lo hi (r₁ ++ r₂)

/-- `addConstraint` prepends, so a symmetry-broken CSP reads `c :: (bounds ++ rest)`: the bounds are
    no longer the prefix.  A non-`bound` `c` is skipped by the scan, so the bounds still read back. -/
theorem extractVariableBounds_of_cons_range_prefix {n : ℕ} (c : IntConstraint n) (hc : NotBound c)
    (lo hi : ℕ → ℤ) (rest : List (IntConstraint n)) (i : Fin n) :
    (IntCSP.mk n (c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
        ++ rest))).extractVariableBounds i = (lo i.val, hi i.val) := by
  show (match ((c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
          ++ rest)).filterMap _) with
        | [] => ((-1000 : ℤ), (1000 : ℤ)) | (lb, ub) :: _ => (lb, ub)) = _
  -- `List.filterMap_cons` is stated for an arbitrary `f`, so it applies to the goal's own matcher;
  -- rewriting with a locally-stated copy would not, as that elaborates to a *different* matcher.
  rw [List.filterMap_cons]
  cases c <;> first
    | exact hc.elim
    | (dsimp only
       rw [List.filterMap_append, List.filterMap_map, Function.comp_def,
           filterMap_range_single n i.val i.isLt (fun x => (lo x, hi x))]
       rfl)

/-- `hbound` for a symmetry-broken `bound`-prefixed CSP (`addConstraint` applied once). -/
theorem hbound_of_cons_range_prefix {n : ℕ} (c : IntConstraint n) (hc : NotBound c)
    (lo hi : ℕ → ℤ) (rest : List (IntConstraint n)) :
    ∀ i : Fin (IntCSP.mk n (c :: ((List.range n).map
        (fun x => IntConstraint.bound x (lo x) (hi x)) ++ rest))).num_vars,
      IntConstraint.bound i.val
          ((IntCSP.mk n (c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ rest))).extractVariableBounds i).1
          ((IntCSP.mk n (c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ rest))).extractVariableBounds i).2
        ∈ (IntCSP.mk n (c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
            ++ rest))).constraints := by
  intro i
  rw [extractVariableBounds_of_cons_range_prefix c hc lo hi rest i]
  exact List.mem_cons_of_mem c
    (List.mem_append_left _ (List.mem_map_of_mem (List.mem_range.mpr i.isLt)))

/-- Same, for a symmetry-broken generator ending `bounds ++ r₁ ++ r₂`. -/
theorem hbound_of_cons_range_prefix₂ {n : ℕ} (c : IntConstraint n) (hc : NotBound c)
    (lo hi : ℕ → ℤ) (r₁ r₂ : List (IntConstraint n)) :
    ∀ i : Fin (IntCSP.mk n (c :: ((List.range n).map
        (fun x => IntConstraint.bound x (lo x) (hi x)) ++ r₁ ++ r₂))).num_vars,
      IntConstraint.bound i.val
          ((IntCSP.mk n (c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ r₁ ++ r₂))).extractVariableBounds i).1
          ((IntCSP.mk n (c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
              ++ r₁ ++ r₂))).extractVariableBounds i).2
        ∈ (IntCSP.mk n (c :: ((List.range n).map (fun x => IntConstraint.bound x (lo x) (hi x))
            ++ r₁ ++ r₂))).constraints := by
  rw [List.append_assoc]
  exact hbound_of_cons_range_prefix c hc lo hi (r₁ ++ r₂)

/-! ### CSP Construction -/

/-- Create empty CSP with specified number of variables -/
def mkEmpty (num_vars : ℕ) : IntCSP where
  num_vars := num_vars
  constraints := []

/-- Add a constraint to an existing CSP -/
def addConstraint (csp : IntCSP)
    (constraint : IntConstraint csp.num_vars) : IntCSP :=
  { csp with constraints := constraint :: csp.constraints }

/-- Add multiple constraints -/
def addConstraints (csp : IntCSP)
    (new_constraints : List (IntConstraint csp.num_vars)) : IntCSP :=
  { csp with constraints := new_constraints ++ csp.constraints }



/-! ### Utility Functions -/

/-- Count constraints in a CSP -/
def constraintCount (csp : IntCSP) : ℕ :=
  csp.constraints.length

/-- Get all variable indices -/
def allVars (csp : IntCSP) : List (VarType csp.num_vars) :=
  List.ofFn id

/-- Helper function to convert a list of natural numbers to a vector of Fin with bounds checking.
    Returns Some with the vector if all inputs are within bounds, None otherwise. -/
def listToFinVector (inputs : List ℕ) (num_nodes : ℕ) :
    Option (Σ n : ℕ, _root_.Vector (Fin num_nodes) n) :=
  -- Filter and map inputs to Fin num_nodes, keeping only valid ones
  let fin_list : List (Fin num_nodes) := inputs.filterMap fun inp =>
    if h : inp < num_nodes then some ⟨inp, h⟩ else none
  -- Check that no inputs were filtered out (all were valid) and list is non-empty
  if fin_list.length = inputs.length ∧ inputs.length > 0 then
    -- Convert to array then to vector
    let arr := Array.mk fin_list
    have h_size : arr.size = fin_list.length := by rfl
    some ⟨fin_list.length, ⟨arr, h_size⟩⟩
  else
    none

end IntCSP

/-! ### Extracting Constraints from Built CSPs -/

/-- Get all constraints from a CSP -/
def getConstraints (csp : IntCSP) : List (IntConstraint csp.num_vars) :=
  csp.constraints

/-- Count total number of constraints -/
def countConstraints (csp : IntCSP) : ℕ :=
  csp.constraints.length

/-- Count constraints of a specific type -/
def countConstraintsByPattern (csp : IntCSP)
    (pred : IntConstraint csp.num_vars → Bool) : ℕ :=
  csp.constraints.filter pred |>.length

/-- Count bound constraints -/
def countBoundConstraints (csp : IntCSP) : ℕ :=
  countConstraintsByPattern csp fun p =>
    match p with
    | IntConstraint.bound _ _ _ => true
    | _ => false



/-! ### Basic Examples -/

section Examples

/-- Example: Simple 2-variable CSP with no constraints -/
def example_2var : IntCSP :=
  IntCSP.mkEmpty 2

/-- Example: CSP with bound constraints -/
def example_with_bounds : IntCSP :=
  let csp := IntCSP.mkEmpty 3
  -- Note: In practice, bounds are added via Builder API
  -- This is just for illustration
  csp

end Examples

end CSP.L2S
