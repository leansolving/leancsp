import CSP.L2S.Backend
import CSP.L2S.Core

namespace CSP.L2S.SMTLIB

open CSP.L2S

/-!
# SMT-LIB backend

Translates IntCSP to SMT-LIB 2.6 format for SMT solvers (Z3, CVC5, etc.).

## Features
- Pattern-based constraint translation
- Automatic logic inference (QF_LIA vs QF_NIA)
- Variable bounds as domain assertions
- Support for 50+ constraint types

-/

/-! ### Helper Functions -/

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

/-! ### Logic Inference -/

/-- Infer SMT-LIB logic from constraint patterns (FIXED: was hardcoded) -/
def inferLogic (csp : IntCSP) : String :=
  let hasNonlinear := csp.constraints.any fun tc =>
    match tc with
    | IntConstraint.product_rel_var vars _ _ => vars.length ≥ 2
    | IntConstraint.modulo _ _ _ => true
    | IntConstraint.xor_gate _ _ _ => true
    | IntConstraint.xor_all _ _ => true
    | _ => false
  if hasNonlinear then "QF_NIA" else "QF_LIA"

/-! ### Pattern Translation -/

/-- Translate a single constraint pattern to SMT-LIB assertion -/
def patternToSMTLIB {num_vars : ℕ} (opts : BackendOptions)
    (pattern : IntConstraint num_vars) : Except TranslatorError (List String) :=
  match pattern with
  -- Global Constraints
  | IntConstraint.alldifferent vars =>
      -- SMT-LIB distinct requires at least 2 arguments
      if vars.length < 2 then .ok []
      else .ok [s!"(assert (distinct {varList vars}))"]

  | IntConstraint.alldifferentOffset vars offsets =>
      -- SMT-LIB distinct requires at least 2 arguments
      if vars.length < 2 then .ok []
      else
        let terms := (vars.zip offsets).map fun (v, off) =>
          if off = 0 then varName v
          else if off > 0 then s!"(+ {varName v} {off})"
          else s!"(- {varName v} {-off})"
        let terms_str := String.intercalate " " terms
        .ok [s!"(assert (distinct {terms_str}))"]

  | IntConstraint.value_precedence _colors =>
      -- Staircase relaxation of value precedence (`x_j ≤ j`), matching the verified PB backend.
      .ok ((List.range num_vars).map (fun j => s!"(assert (<= {varName j} {j}))"))

  | IntConstraint.increasing vars =>
      -- FIXED: was using tail!, now using drop
      let pairs := List.zip vars (vars.drop 1)
      let conjuncts := pairs.map fun (v1, v2) => s!"(<= {varName v1} {varName v2})"
      let conj_str := String.intercalate " " conjuncts
      .ok [s!"(assert (and {conj_str}))"]

  -- Arithmetic Constraints
  | IntConstraint.sum vars op target =>
      let sum_expr := s!"(+ {varList vars})"
      let assertion := assertRel op sum_expr (formatInt target)
      .ok [s!"(assert {assertion})"]

  | IntConstraint.linear vars coeffs op target =>
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
  | IntConstraint.count vars value n =>
      let reified := vars.map fun v => s!"(ite (= {varName v} {formatInt value}) 1 0)"
      let sum_expr := s!"(+ {String.intercalate " " reified})"
      .ok [s!"(assert (= {sum_expr} {formatInt n}))"]

  | IntConstraint.count_var vars value count_var =>
      let reified := vars.map fun v => s!"(ite (= {varName v} {formatInt value}) 1 0)"
      let sum_expr := s!"(+ {String.intercalate " " reified})"
      .ok [s!"(assert (= {sum_expr} {varName count_var}))"]

  -- Element Constraint (Array Indexing via Nested ITE)
  | IntConstraint.element index array result =>
      let rec buildITE (idx : ℕ) (vals : List ℤ) : String :=
        match vals with
        | [] => "false"
        | [last] => s!"(= {varName result} {formatInt last})"
        | first :: rest =>
            s!"(ite (= {varName index} {idx + 1}) (= {varName result} {formatInt first}) {buildITE (idx + 1) rest})"
      .ok [s!"(assert {buildITE 0 array})"]

  -- Maximum/Minimum
  | IntConstraint.maximum vars maxVar =>
      let ge_conjuncts := vars.map fun v => s!"(>= {varName maxVar} {varName v})"
      let eq_disjuncts := vars.map fun v => s!"(= {varName maxVar} {varName v})"
      let ge_str := String.intercalate " " ge_conjuncts
      let eq_str := String.intercalate " " eq_disjuncts
      .ok [s!"(assert (and (and {ge_str}) (or {eq_str})))"]

  | IntConstraint.minimum vars minVar =>
      let le_conjuncts := vars.map fun v => s!"(<= {varName minVar} {varName v})"
      let eq_disjuncts := vars.map fun v => s!"(= {varName minVar} {varName v})"
      let le_str := String.intercalate " " le_conjuncts
      let eq_str := String.intercalate " " eq_disjuncts
      .ok [s!"(assert (and (and {le_str}) (or {eq_str})))"]

  -- Bound Constraints
  | IntConstraint.bound var lb ub =>
      .ok [s!"(assert (and (>= {varName var} {formatInt lb}) (<= {varName var} {formatInt ub})))"]

  -- Binary Comparison Constraints
  | IntConstraint.eq var1 var2 =>
      .ok [s!"(assert (= {varName var1} {varName var2}))"]

  | IntConstraint.ne var1 var2 =>
      .ok [s!"(assert (distinct {varName var1} {varName var2}))"]  -- FIXED

  | IntConstraint.lt var1 var2 =>
      .ok [s!"(assert (< {varName var1} {varName var2}))"]

  | IntConstraint.le var1 var2 =>
      .ok [s!"(assert (<= {varName var1} {varName var2}))"]

  | IntConstraint.gt var1 var2 =>
      .ok [s!"(assert (> {varName var1} {varName var2}))"]

  | IntConstraint.ge var1 var2 =>
      .ok [s!"(assert (>= {varName var1} {varName var2}))"]

  -- Unary Comparison Constraints
  | IntConstraint.eq_const var value =>
      .ok [s!"(assert (= {varName var} {formatInt value}))"]

  | IntConstraint.ne_const var value =>
      .ok [s!"(assert (distinct {varName var} {formatInt value}))"]  -- FIXED

  | IntConstraint.lt_const var value =>
      .ok [s!"(assert (< {varName var} {formatInt value}))"]

  | IntConstraint.le_const var value =>
      .ok [s!"(assert (<= {varName var} {formatInt value}))"]

  | IntConstraint.gt_const var value =>
      .ok [s!"(assert (> {varName var} {formatInt value}))"]

  | IntConstraint.ge_const var value =>
      .ok [s!"(assert (>= {varName var} {formatInt value}))"]

  -- Logical/Disjunctive Constraints
  | IntConstraint.schur_triple var1 var2 var3 =>
      .ok [s!"(assert (or (distinct {varName var1} {varName var2}) (distinct {varName var1} {varName var3}) (distinct {varName var2} {varName var3})))"]

  -- Absolute Value Constraints
  | IntConstraint.abs_diff_rel var1 var2 op target =>
      let abs_expr := s!"(abs (- {varName var1} {varName var2}))"
      let assertion := assertRel op abs_expr (formatInt target)
      .ok [s!"(assert {assertion})"]

  | IntConstraint.abs_diff_var var1 var2 result =>
      let abs_expr := s!"(abs (- {varName var1} {varName var2}))"
      .ok [s!"(assert (= {varName result} {abs_expr}))"]

  -- Modulo Constraints
  | IntConstraint.modulo var n k =>
      .ok [s!"(assert (= (mod {varName var} {formatInt n}) {formatInt k}))"]

  -- Sliding Window Constraints
  | IntConstraint.sliding_sum vars window_size op target =>
      let num_windows := vars.length - window_size + 1
      let window_assertions := List.range num_windows |>.map fun i =>
        let window_vars := vars.drop i |>.take window_size
        let sum_expr := s!"(+ {varList window_vars})"
        assertRel op sum_expr (formatInt target)
      let assertions_str := String.intercalate " " window_assertions
      .ok [s!"(assert (and {assertions_str}))"]

  -- Boolean Gate Constraints
  | IntConstraint.not_gate in1 out =>
      .ok [s!"(assert (= {varName out} (ite (= {varName in1} 1) 0 1)))"]

  | IntConstraint.and_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (and (= {varName in1} 1) (= {varName in2} 1)) 1 0)))"]

  | IntConstraint.or_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (or (= {varName in1} 1) (= {varName in2} 1)) 1 0)))"]

  | IntConstraint.xor_gate in1 in2 out =>
      .ok [s!"(assert (and (= {varName out} (mod (+ {varName in1} {varName in2}) 2)) (<= {varName out} 1) (>= {varName out} 0)))"]

  | IntConstraint.nand_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (and (= {varName in1} 1) (= {varName in2} 1)) 0 1)))"]

  | IntConstraint.nor_gate in1 in2 out =>
      .ok [s!"(assert (= {varName out} (ite (or (= {varName in1} 1) (= {varName in2} 1)) 0 1)))"]

  -- Multi-input Logical Operations
  | IntConstraint.and_all vars result =>
      let all_ones := vars.map fun v => s!"(= {varName v} 1)"
      let conj_str := String.intercalate " " all_ones
      .ok [s!"(assert (= {varName result} (ite (and {conj_str}) 1 0)))"]

  | IntConstraint.or_all vars result =>
      let any_one := vars.map fun v => s!"(= {varName v} 1)"
      let disj_str := String.intercalate " " any_one
      .ok [s!"(assert (= {varName result} (ite (or {disj_str}) 1 0)))"]

  | IntConstraint.xor_all vars result =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (and (= {varName result} (mod {sum_expr} 2)) (<= {varName result} 1) (>= {varName result} 0)))"]

  -- Implication and Equivalence
  | IntConstraint.implies premise conclusion =>
      .ok [s!"(assert (>= {varName conclusion} {varName premise}))"]

  | IntConstraint.iff var1 var2 =>
      .ok [s!"(assert (= {varName var1} {varName var2}))"]

  | IntConstraint.if_then var value next_var next_value =>
      .ok [s!"(assert (=> (= {varName var} {formatInt value}) (= {varName next_var} {formatInt next_value})))"]

  | IntConstraint.if_then_or var value next_var allowed_values =>
      let eq_disjuncts := allowed_values.map fun v => s!"(= {varName next_var} {formatInt v})"
      let disj_str := String.intercalate " " eq_disjuncts
      .ok [s!"(assert (=> (= {varName var} {formatInt value}) (or {disj_str})))"]

  -- Cardinality Constraints
  | IntConstraint.at_least_k vars k =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (>= {sum_expr} {formatInt k}))"]

  | IntConstraint.at_most_k vars k =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (<= {sum_expr} {formatInt k}))"]

  | IntConstraint.exactly_k vars k =>
      let sum_expr := s!"(+ {varList vars})"
      .ok [s!"(assert (= {sum_expr} {formatInt k}))"]

  -- Arithmetic Constraints with Variable Targets
  | IntConstraint.sum_rel_var vars op target_var =>
      let sum_expr := s!"(+ {varList vars})"
      let assertion := assertRel op sum_expr (varName target_var)
      .ok [s!"(assert {assertion})"]

  | IntConstraint.linear_rel_var vars coeffs op target_var =>
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

  | IntConstraint.product_rel_var vars op target_var =>
      let product_expr := match vars with
        | [] => "1"
        | [single] => varName single
        | _ => s!"(* {varList vars})"
      let assertion := assertRel op product_expr (varName target_var)
      .ok [s!"(assert {assertion})"]

  -- Scheduling Constraints
  | IntConstraint.disjunctive tasks durs =>
      let task_dur_pairs := tasks.zip durs
      let pairs := List.product task_dur_pairs task_dur_pairs |>.filter fun ((i, _), (j, _)) => i < j
      let disjuncts := pairs.map fun ((i, dur_i), (j, dur_j)) =>
        s!"(or (<= (+ {varName i} {formatInt dur_i}) {varName j}) (<= (+ {varName j} {formatInt dur_j}) {varName i}))"
      let disj_str := String.intercalate " " disjuncts
      .ok [s!"(assert (and {disj_str}))"]

  | IntConstraint.strictLexRevLeader =>
      -- `x <_lex rev(x)` unfolded to nested or/and: compare `x_i` with `x_{n-1-i}`.
      let n := num_vars
      let body := (List.range n).reverse.foldl (fun acc i =>
        let xi := varName i
        let xr := varName (n - 1 - i)
        s!"(or (< {xi} {xr}) (and (= {xi} {xr}) {acc}))") "false"
      .ok [s!"(assert {body})"]

  | IntConstraint.unknown _ scope =>
      .error ⟨s!"Unknown constraint on variables: {scope}"⟩

/-! ### Backend Instance -/

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
    | IntConstraint.bound _ _ _ => true  -- Handled in domainAsserts
    | _ => false

/-! ### Public API -/

/-- Convenience wrapper (backward compatibility) -/
def translateToSMTLIB (csp : IntCSP) : String :=
  match translateWith smtlibBackend default csp with
  | .ok s => s
  | .error e => s!"; Error: {e.msg}"

/-- Convenience wrapper with custom logic -/
def translateToSMTLIBWithLogic (csp : IntCSP) (logic : String) : String :=
  match translateWith smtlibBackend { smtLogic := some logic } csp with
  | .ok s => s
  | .error e => s!"; Error: {e.msg}"

/-- Convenience wrapper with strict mode -/
def translateToSMTLIBStrict (csp : IntCSP) : Except TranslatorError String :=
  translateWith smtlibBackend { strict := true } csp

end CSP.L2S.SMTLIB
