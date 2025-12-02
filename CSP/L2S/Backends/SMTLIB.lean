import CSP.L2S.Backend
import CSP.L2S.Core

namespace CSP.L2S.SMTLIB

open CSP.L2S

/-!
# SMT-LIB Backend for L2M

Translates HomogeneousCSP to SMT-LIB 2.6 format for SMT solvers (Z3, CVC5, etc.).

## Features
- Pattern-based constraint translation
- Automatic logic inference (QF_LIA vs QF_NIA)
- Variable bounds as domain assertions
- Support for 50+ constraint types

-/

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Format a variable as x{n} -/
def varName (n : ℕ) : String := s!"x{n}"

/-- Format a list of variables as space-separated -/
def varList (vars : List ℕ) : String :=
  String.intercalate " " (vars.map varName)

/-- Format an integer constant in SMT-LIB syntax (wrap negatives) -/
def formatInt (n : ℤ) : String :=
  if n < 0 then s!"(- {-n})" else toString n

/-- Build SMT-LIB relational assertion -/
def assertRel (op : RelOp) (lhs rhs : String) : String :=
  match op with
  | RelOp.EQ => s!"(= {lhs} {rhs})"
  | RelOp.NE => s!"(distinct {lhs} {rhs})"
  | RelOp.LT => s!"(< {lhs} {rhs})"
  | RelOp.LE => s!"(<= {lhs} {rhs})"
  | RelOp.GT => s!"(> {lhs} {rhs})"
  | RelOp.GE => s!"(>= {lhs} {rhs})"

-- ============================================================================
-- Logic Inference
-- ============================================================================

/-- Infer SMT-LIB logic from constraint patterns (FIXED: was hardcoded) -/
def inferLogic (csp : HomogeneousCSP) : String :=
  let hasNonlinear := csp.constraints.any fun tc =>
    match tc.pattern with
    | ConstraintPattern.product_rel_var vars _ _ => vars.length ≥ 2
    | ConstraintPattern.modulo _ _ _ => true
    | ConstraintPattern.xor_gate _ _ _ => true
    | ConstraintPattern.xor_all _ _ => true
    | _ => false
  if hasNonlinear then "QF_NIA" else "QF_LIA"

-- ============================================================================
-- Pattern Translation
-- ============================================================================

/-- Translate a single constraint pattern to SMT-LIB assertion -/
def patternToSMTLIB {num_vars : ℕ} (opts : BackendOptions)
    (pattern : ConstraintPattern num_vars) : Except TranslatorError (List String) :=
  match pattern with
  -- Global Constraints
  | ConstraintPattern.alldifferent vars =>
      -- SMT-LIB distinct requires at least 2 arguments
      if vars.length < 2 then .ok []
      else .ok [s!"(assert (distinct {varList vars}))"]

  | ConstraintPattern.alldifferentOffset vars offsets =>
      -- SMT-LIB distinct requires at least 2 arguments
      if vars.length < 2 then .ok []
      else
        let terms := (vars.zip offsets).map fun (v, off) =>
          if off = 0 then varName v
          else if off > 0 then s!"(+ {varName v} {off})"
          else s!"(- {varName v} {-off})"
        let terms_str := String.intercalate " " terms
        .ok [s!"(assert (distinct {terms_str}))"]

  | ConstraintPattern.increasing vars =>
      -- FIXED: was using tail!, now using drop
      let pairs := List.zip vars (vars.drop 1)
      let conjuncts := pairs.map fun (v1, v2) => s!"(<= {varName v1} {varName v2})"
      let conj_str := String.intercalate " " conjuncts
      .ok [s!"(assert (and {conj_str}))"]

  -- Arithmetic Constraints
  | ConstraintPattern.sum vars op target =>
      let sum_expr := s!"(+ {varList vars})"
      let assertion := assertRel op sum_expr (formatInt target)
      .ok [s!"(assert {assertion})"]

  | ConstraintPattern.linear vars coeffs op target =>
      let terms := (vars.zip coeffs).map fun (v, c) =>
        if c = 1 then varName v
        else if c = -1 then s!"(- {varName v})"
        else if c < 0 then s!"(* (- {-c}) {varName v})"
        else s!"(* {c} {varName v})"
      let sum_expr := match terms with
        | [] => "0"
        | [single] => single
        | _ => s!"(+ {String.intercalate " " terms})"
      let assertion := assertRel op sum_expr (formatInt target)
      .ok [s!"(assert {assertion})"]

  -- Count Constraint (Reified)
  | ConstraintPattern.count vars value n =>
      let reified := vars.map fun v => s!"(ite (= {varName v} {formatInt value}) 1 0)"
      let sum_expr := s!"(+ {String.intercalate " " reified})"
      .ok [s!"(assert (= {sum_expr} {formatInt n}))"]

  | ConstraintPattern.count_var vars value count_var =>
      let reified := vars.map fun v => s!"(ite (= {varName v} {formatInt value}) 1 0)"
      let sum_expr := s!"(+ {String.intercalate " " reified})"
      .ok [s!"(assert (= {sum_expr} {varName count_var}))"]

  -- Element Constraint (Array Indexing via Nested ITE)
  | ConstraintPattern.element index array result =>
      let rec buildITE (idx : ℕ) (vals : List ℤ) : String :=
        match vals with
        | [] => "false"
        | [last] => s!"(= {varName result} {formatInt last})"
        | first :: rest =>
            s!"(ite (= {varName index} {idx + 1}) (= {varName result} {formatInt first}) {buildITE (idx + 1) rest})"
      .ok [s!"(assert {buildITE 0 array})"]

  -- Maximum/Minimum
  | ConstraintPattern.maximum vars maxVar =>
      let ge_conjuncts := vars.map fun v => s!"(>= {varName maxVar} {varName v})"
      let eq_disjuncts := vars.map fun v => s!"(= {varName maxVar} {varName v})"
      let ge_str := String.intercalate " " ge_conjuncts
      let eq_str := String.intercalate " " eq_disjuncts
      .ok [s!"(assert (and (and {ge_str}) (or {eq_str})))"]

  | ConstraintPattern.minimum vars minVar =>
      let le_conjuncts := vars.map fun v => s!"(<= {varName minVar} {varName v})"
      let eq_disjuncts := vars.map fun v => s!"(= {varName minVar} {varName v})"
      let le_str := String.intercalate " " le_conjuncts
      let eq_str := String.intercalate " " eq_disjuncts
      .ok [s!"(assert (and (and {le_str}) (or {eq_str})))"]

  -- Bound Constraints
  | ConstraintPattern.bound var lb ub =>
      .ok [s!"(assert (and (>= {varName var} {formatInt lb}) (<= {varName var} {formatInt ub})))"]

  -- Binary Comparison Constraints
  | ConstraintPattern.eq var1 var2 =>
      .ok [s!"(assert (= {varName var1} {varName var2}))"]

  | ConstraintPattern.ne var1 var2 =>
      .ok [s!"(assert (distinct {varName var1} {varName var2}))"]  -- FIXED

  | ConstraintPattern.lt var1 var2 =>
      .ok [s!"(assert (< {varName var1} {varName var2}))"]

  | ConstraintPattern.le var1 var2 =>
      .ok [s!"(assert (<= {varName var1} {varName var2}))"]

  | ConstraintPattern.gt var1 var2 =>
      .ok [s!"(assert (> {varName var1} {varName var2}))"]

  | ConstraintPattern.ge var1 var2 =>
      .ok [s!"(assert (>= {varName var1} {varName var2}))"]

  -- Unary Comparison Constraints
  | ConstraintPattern.eq_const var value =>
      .ok [s!"(assert (= {varName var} {formatInt value}))"]

  | ConstraintPattern.ne_const var value =>
      .ok [s!"(assert (distinct {varName var} {formatInt value}))"]  -- FIXED

  | ConstraintPattern.lt_const var value =>
      .ok [s!"(assert (< {varName var} {formatInt value}))"]

  | ConstraintPattern.le_const var value =>
      .ok [s!"(assert (<= {varName var} {formatInt value}))"]

  | ConstraintPattern.gt_const var value =>
      .ok [s!"(assert (> {varName var} {formatInt value}))"]

  | ConstraintPattern.ge_const var value =>
      .ok [s!"(assert (>= {varName var} {formatInt value}))"]

  -- Logical/Disjunctive Constraints
  | ConstraintPattern.schur_triple var1 var2 var3 =>
      .ok [s!"(assert (or (distinct {varName var1} {varName var2}) (distinct {varName var1} {varName var3}) (distinct {varName var2} {varName var3})))"]

  -- Absolute Value Constraints
  | ConstraintPattern.abs_diff_rel var1 var2 op target =>
      let abs_expr := s!"(abs (- {varName var1} {varName var2}))"
      let assertion := assertRel op abs_expr (formatInt target)
      .ok [s!"(assert {assertion})"]

  | ConstraintPattern.abs_diff_var var1 var2 result =>
      let abs_expr := s!"(abs (- {varName var1} {varName var2}))"
      .ok [s!"(assert (= {varName result} {abs_expr}))"]

  -- Modulo Constraints
  | ConstraintPattern.modulo var n k =>
      .ok [s!"(assert (= (mod {varName var} {formatInt n}) {formatInt k}))"]

  -- Sliding Window Constraints
  | ConstraintPattern.sliding_sum vars window_size op target =>
      let num_windows := vars.length - window_size + 1
      let window_assertions := List.range num_windows |>.map fun i =>
        let window_vars := vars.drop i |>.take window_size
        let sum_expr := s!"(+ {varList window_vars})"
        assertRel op sum_expr (formatInt target)
      let assertions_str := String.intercalate " " window_assertions
      .ok [s!"(assert (and {assertions_str}))"]

  -- Boolean Gate Constraints
  | ConstraintPattern.not_gate in1 out =>
      .ok [s!"(assert (= {varName out} (ite (= {varName in1} 1) 0 1)))"]

  | ConstraintPattern.and_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (and (= {varName in1} 1) (= {varName in2} 1)) 1 0)))"]

  | ConstraintPattern.or_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (or (= {varName in1} 1) (= {varName in2} 1)) 1 0)))"]

  | ConstraintPattern.xor_gate in1 in2 out =>
      .ok [s!"(assert (and (= {varName out} (mod (+ {varName in1} {varName in2}) 2)) (<= {varName out} 1) (>= {varName out} 0)))"]

  | ConstraintPattern.nand_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (and (= {varName in1} 1) (= {varName in2} 1)) 0 1)))"]

  | ConstraintPattern.nor_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (or (= {varName in1} 1) (= {varName in2} 1)) 0 1)))"]

  -- Multi-input Logical Operations
  | ConstraintPattern.and_all vars result =>
      let all_ones := vars.map fun v => s!"(= {varName v} 1)"
      let conj_str := String.intercalate " " all_ones
      .ok [s!"(assert (= {varName result} (ite (and {conj_str}) 1 0)))"]

  | ConstraintPattern.or_all vars result =>
      let any_one := vars.map fun v => s!"(= {varName v} 1)"
      let disj_str := String.intercalate " " any_one
      .ok [s!"(assert (= {varName result} (ite (or {disj_str}) 1 0)))"]

  | ConstraintPattern.xor_all vars result =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (and (= {varName result} (mod {sum_expr} 2)) (<= {varName result} 1) (>= {varName result} 0)))"]

  -- Implication and Equivalence
  | ConstraintPattern.implies premise conclusion =>
      .ok [s!"(assert (>= {varName conclusion} {varName premise}))"]

  | ConstraintPattern.iff var1 var2 =>
      .ok [s!"(assert (= {varName var1} {varName var2}))"]

  | ConstraintPattern.if_then var value next_var next_value =>
      .ok [s!"(assert (=> (= {varName var} {formatInt value}) (= {varName next_var} {formatInt next_value})))"]

  | ConstraintPattern.if_then_or var value next_var allowed_values =>
      let eq_disjuncts := allowed_values.map fun v => s!"(= {varName next_var} {formatInt v})"
      let disj_str := String.intercalate " " eq_disjuncts
      .ok [s!"(assert (=> (= {varName var} {formatInt value}) (or {disj_str})))"]

  -- Cardinality Constraints
  | ConstraintPattern.at_least_k vars k =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (>= {sum_expr} {formatInt k}))"]

  | ConstraintPattern.at_most_k vars k =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (<= {sum_expr} {formatInt k}))"]

  | ConstraintPattern.exactly_k vars k =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (= {sum_expr} {formatInt k}))"]

  -- Arithmetic Constraints with Variable Targets
  | ConstraintPattern.sum_rel_var vars op target_var =>
      let sum_expr := s!"(+ {varList vars})"
      let assertion := assertRel op sum_expr (varName target_var)
      .ok [s!"(assert {assertion})"]

  | ConstraintPattern.linear_rel_var vars coeffs op target_var =>
      let terms := (vars.zip coeffs).map fun (v, c) =>
        if c = 1 then varName v
        else if c = -1 then s!"(- {varName v})"
        else if c < 0 then s!"(* (- {-c}) {varName v})"
        else s!"(* {c} {varName v})"
      let sum_expr := match terms with
        | [] => "0"
        | [single] => single
        | _ => s!"(+ {String.intercalate " " terms})"
      let assertion := assertRel op sum_expr (varName target_var)
      .ok [s!"(assert {assertion})"]

  | ConstraintPattern.product_rel_var vars op target_var =>
      let product_expr := match vars with
        | [] => "1"
        | [single] => varName single
        | _ => s!"(* {varList vars})"
      let assertion := assertRel op product_expr (varName target_var)
      .ok [s!"(assert {assertion})"]

  -- Scheduling Constraints
  | ConstraintPattern.disjunctive tasks durs =>
      let task_dur_pairs := tasks.zip durs
      let pairs := List.product task_dur_pairs task_dur_pairs |>.filter fun ((i, _), (j, _)) => i < j
      let disjuncts := pairs.map fun ((i, dur_i), (j, dur_j)) =>
        s!"(or (<= (+ {varName i} {formatInt dur_i}) {varName j}) (<= (+ {varName j} {formatInt dur_j}) {varName i}))"
      let disj_str := String.intercalate " " disjuncts
      .ok [s!"(assert (and {disj_str}))"]

  | ConstraintPattern.unknown _ scope =>
      .error ⟨s!"Unknown constraint on variables: {scope}"⟩

-- ============================================================================
-- Backend Instance
-- ============================================================================

/-- SMT-LIB backend instance -/
def smtlibBackend : Backend where
  name := "SMT-LIB"

  header := fun csp opts =>
    let logic := match opts.smtLogic with
      | some l => l
      | none => if opts.inferLogic then inferLogic csp else "QF_LIA"
    ["; Generated by L2S (LeanToSolver)", s!"(set-logic {logic})", ""]

  footer := fun csp opts =>
    ["", "(check-sat)", "(get-model)"]

  varDecls := fun csp bounds =>
    List.ofFn fun (i : Fin csp.num_vars) =>
      s!"(declare-const {varName i.val} Int)"

  domainAsserts := fun csp bounds =>
    List.ofFn fun (i : Fin csp.num_vars) =>
      let (lb, ub) := bounds i
      s!"(assert (and (>= {varName i.val} {formatInt lb}) (<= {varName i.val} {formatInt ub})))"

  translatePattern := patternToSMTLIB

  skipInConstraints := fun pattern =>
    match pattern with
    | ConstraintPattern.bound _ _ _ => true  -- Handled in domainAsserts
    | _ => false

-- ============================================================================
-- Public API
-- ============================================================================

/-- Convenience wrapper (backward compatibility) -/
def translateToSMTLIB (csp : HomogeneousCSP) : String :=
  match translateWith smtlibBackend default csp with
  | .ok s => s
  | .error e => s!"; Error: {e.msg}"

/-- Convenience wrapper with custom logic -/
def translateToSMTLIBWithLogic (csp : HomogeneousCSP) (logic : String) : String :=
  match translateWith smtlibBackend { smtLogic := some logic } csp with
  | .ok s => s
  | .error e => s!"; Error: {e.msg}"

/-- Convenience wrapper with strict mode -/
def translateToSMTLIBStrict (csp : HomogeneousCSP) : Except TranslatorError String :=
  translateWith smtlibBackend { strict := true } csp

end CSP.L2S.SMTLIB
