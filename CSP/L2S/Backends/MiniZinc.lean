import CSP.L2S.Backend
import CSP.L2S.Core

namespace CSP.L2S.MiniZinc

open CSP.L2S

/-!
# MiniZinc Backend for L2M

Translates IntCSP to MiniZinc constraint programming language.

## Features
- Pattern-based constraint translation
- Automatic include generation
- Variable bounds from constraint patterns
- Support for 50+ constraint types
-/

-- ============================================================================
-- Helper Functions
-- ============================================================================

/-- Convert RelOp to MiniZinc operator string -/
def relOpToMzn (op : RelOp) : String :=
  match op with
  | RelOp.EQ => "="
  | RelOp.NE => "!="
  | RelOp.LT => "<"
  | RelOp.LE => "<="
  | RelOp.GT => ">"
  | RelOp.GE => ">="

-- ============================================================================
-- Pattern Translation
-- ============================================================================

/-- Translate a single constraint pattern to MiniZinc constraint syntax -/
def patternToMiniZinc {num_vars : ℕ} (opts : BackendOptions)
    (pattern : IntConstraint num_vars) : Except TranslatorError (List String) :=
  match pattern with
  | IntConstraint.alldifferent vars =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint alldifferent([{varList}]);"]

  | IntConstraint.alldifferentOffset vars offsets =>
      let terms := (vars.zip offsets).map fun (v, off) =>
        if off ≥ 0 then s!"x{v} + {off}" else s!"x{v} - {-off}"
      let termList := String.intercalate ", " terms
      .ok [s!"constraint alldifferent([{termList}]);"]

  | IntConstraint.increasing vars =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint increasing([{varList}]);"]

  | IntConstraint.sum vars op target =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      let opStr := relOpToMzn op
      .ok [s!"constraint sum([{varList}]) {opStr} {target};"]

  | IntConstraint.linear vars coeffs op target =>
      let terms := (vars.zip coeffs).map fun (v, c) => s!"({c})*x{v}"
      let exprStr := String.intercalate " + " terms
      let opStr := relOpToMzn op
      .ok [s!"constraint {exprStr} {opStr} {target};"]

  | IntConstraint.count vars value n =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint count([{varList}], {value}, {n});"]

  | IntConstraint.count_var vars value count_var =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint count([{varList}], {value}, x{count_var});"]

  | IntConstraint.element index array result =>
      let arrayStr := array.map toString |> String.intercalate ", "
      .ok [s!"constraint element(x{index}, [{arrayStr}], x{result});"]

  | IntConstraint.maximum vars maxVar =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint maximum(x{maxVar}, [{varList}]);"]

  | IntConstraint.minimum vars minVar =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint minimum(x{minVar}, [{varList}]);"]

  | IntConstraint.bound var lb ub =>
      .ok [s!"% Bound constraint x{var} ∈ [{lb}, {ub}] handled in variable declaration"]

  -- Binary comparison constraints
  | IntConstraint.eq var1 var2 =>
      .ok [s!"constraint x{var1} = x{var2};"]

  | IntConstraint.ne var1 var2 =>
      .ok [s!"constraint x{var1} != x{var2};"]

  | IntConstraint.lt var1 var2 =>
      .ok [s!"constraint x{var1} < x{var2};"]

  | IntConstraint.le var1 var2 =>
      .ok [s!"constraint x{var1} <= x{var2};"]

  | IntConstraint.gt var1 var2 =>
      .ok [s!"constraint x{var1} > x{var2};"]

  | IntConstraint.ge var1 var2 =>
      .ok [s!"constraint x{var1} >= x{var2};"]

  -- Unary comparison constraints
  | IntConstraint.eq_const var value =>
      .ok [s!"constraint x{var} = {value};"]

  | IntConstraint.ne_const var value =>
      .ok [s!"constraint x{var} != {value};"]

  | IntConstraint.lt_const var value =>
      .ok [s!"constraint x{var} < {value};"]

  | IntConstraint.le_const var value =>
      .ok [s!"constraint x{var} <= {value};"]

  | IntConstraint.gt_const var value =>
      .ok [s!"constraint x{var} > {value};"]

  | IntConstraint.ge_const var value =>
      .ok [s!"constraint x{var} >= {value};"]

  -- Logical/Disjunctive constraints
  | IntConstraint.schur_triple var1 var2 var3 =>
      .ok [s!"constraint x{var1} != x{var2} \\/ x{var1} != x{var3} \\/ x{var2} != x{var3};"]

  -- Absolute value constraints
  | IntConstraint.abs_diff_rel var1 var2 op target =>
      let opStr := relOpToMzn op
      .ok [s!"constraint abs(x{var1} - x{var2}) {opStr} {target};"]

  | IntConstraint.abs_diff_var var1 var2 result =>
      .ok [s!"constraint x{result} = abs(x{var1} - x{var2});"]

  -- Modulo constraints
  | IntConstraint.modulo var n k =>
      .ok [s!"constraint x{var} mod {n} = {k};"]

  -- Sliding window constraints
  | IntConstraint.sliding_sum vars window_size op target =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      let opStr := relOpToMzn op
      .ok [s!"constraint forall(i in 1..{vars.length - window_size + 1}) (sum([{varList}][i..i+{window_size}-1]) {opStr} {target});"]

  -- Boolean gate constraints
  | IntConstraint.not_gate in1 out =>
      .ok [s!"constraint x{out} = 1 - x{in1};"]

  | IntConstraint.and_gate in1 in2 out =>
      .ok [s!"constraint x{out} = min(x{in1}, x{in2});"]

  | IntConstraint.or_gate in1 in2 out =>
      .ok [s!"constraint x{out} = max(x{in1}, x{in2});"]

  | IntConstraint.xor_gate in1 in2 out =>
      .ok [s!"constraint (x{in1} + x{in2}) mod 2 = x{out};"]

  | IntConstraint.nand_gate in1 in2 out =>
      .ok [s!"constraint x{out} >= 1 - x{in1} /\\ x{out} >= 1 - x{in2} /\\ x{out} <= 2 - x{in1} - x{in2};"]

  | IntConstraint.nor_gate in1 in2 out =>
      .ok [s!"constraint x{out} <= 1 - x{in1} /\\ x{out} <= 1 - x{in2} /\\ x{out} >= 1 - x{in1} - x{in2};"]

  -- Multi-input logical operations
  | IntConstraint.and_all vars result =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint x{result} = min([{varList}]);"]

  | IntConstraint.or_all vars result =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint x{result} = max([{varList}]);"]

  | IntConstraint.xor_all vars result =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) mod 2 = x{result};"]

  -- Implication and equivalence
  | IntConstraint.implies premise conclusion =>
      .ok [s!"constraint x{conclusion} >= x{premise};"]

  | IntConstraint.iff var1 var2 =>
      .ok [s!"constraint x{var1} = x{var2};"]

  | IntConstraint.if_then var value next_var next_value =>
      .ok [s!"constraint (x{var} = {value}) -> (x{next_var} = {next_value});"]

  | IntConstraint.if_then_or var value next_var allowed_values =>
      let set_literal := "{" ++ String.intercalate ", " (allowed_values.map toString) ++ "}"
      .ok [s!"constraint (x{var} = {value}) -> (x{next_var} in {set_literal});"]

  -- Cardinality constraints
  | IntConstraint.at_least_k vars k =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) >= {k};"]

  | IntConstraint.at_most_k vars k =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) <= {k};"]

  | IntConstraint.exactly_k vars k =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) = {k};"]

  -- Arithmetic constraints with variable targets
  | IntConstraint.product_rel_var vars op target_var =>
      let productTerms := vars.map (s!"x{·}") |> String.intercalate " * "
      let opStr := relOpToMzn op
      .ok [s!"constraint ({productTerms}) {opStr} x{target_var};"]

  | IntConstraint.linear_rel_var vars coeffs op target_var =>
      let terms := List.zip vars coeffs |>
        List.map (fun (v, c) =>
          if c = 1 then s!"x{v}"
          else if c = -1 then s!"(-x{v})"
          else s!"({c})*x{v}") |>
        String.intercalate " + "
      let opStr := relOpToMzn op
      .ok [s!"constraint ({terms}) {opStr} x{target_var};"]

  | IntConstraint.sum_rel_var vars op target_var =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      let opStr := relOpToMzn op
      .ok [s!"constraint sum([{varList}]) {opStr} x{target_var};"]

  | IntConstraint.disjunctive tasks durs =>
      let task_vars := "[" ++ String.intercalate ", " (tasks.map (s!"x{·}")) ++ "]"
      let dur_vals := "[" ++ String.intercalate ", " (durs.map toString) ++ "]"
      .ok [s!"constraint disjunctive({task_vars}, {dur_vals});"]

  | IntConstraint.unknown _ scope =>
      .error ⟨s!"Unknown constraint on variables: {scope}"⟩

-- ============================================================================
-- Include Generation
-- ============================================================================

/-- Get required MiniZinc include statements for the constraints -/
def getRequiredIncludes (csp : IntCSP) : List String :=
  let patterns := csp.constraints
  let includes := patterns.foldl (fun acc p =>
    match p with
    | IntConstraint.alldifferent _ => "alldifferent" :: acc
    | IntConstraint.alldifferentOffset _ _ => "alldifferent" :: acc
    | IntConstraint.increasing _ => "globals" :: acc
    | IntConstraint.count _ _ _ => "count" :: acc
    | IntConstraint.count_var _ _ _ => "count" :: acc
    | IntConstraint.element _ _ _ => "element" :: acc
    | IntConstraint.maximum _ _ => "maximum" :: acc
    | IntConstraint.minimum _ _ => "minimum" :: acc
    | IntConstraint.disjunctive _ _ => "disjunctive" :: acc
    | IntConstraint.bound _ _ _ => acc
    | _ => acc
  ) []
  includes.eraseDup.map (s!"include \"{·}.mzn\";")

-- ============================================================================
-- Backend Instance
-- ============================================================================

/-- MiniZinc backend instance -/
def miniZincBackend : Backend where
  name := "MiniZinc"

  header := fun csp opts =>
    ["% Generated by L2S (LeanToSolver)", ""] ++ getRequiredIncludes csp ++ [""]

  footer := fun csp opts =>
    ["", "solve satisfy;"]

  varDecls := fun csp bounds =>
    List.ofFn fun (i : Fin csp.num_vars) =>
      let (lb, ub) := bounds i
      s!"var {lb}..{ub}: x{i.val};"

  domainAsserts := fun csp bounds =>
    []  -- MiniZinc includes bounds in var declarations

  translatePattern := patternToMiniZinc

  skipInConstraints := fun pattern =>
    match pattern with
    | IntConstraint.bound _ _ _ => true
    | _ => false

-- ============================================================================
-- Public API
-- ============================================================================

/-- Convenience wrapper (backward compatibility) -/
def translateToMiniZinc (csp : IntCSP) : String :=
  match translateWith miniZincBackend default csp with
  | .ok s => s
  | .error e => s!"% Error: {e.msg}"

/-- Convenience wrapper with options -/
def translateToMiniZincStrict (csp : IntCSP) : Except TranslatorError String :=
  translateWith miniZincBackend { strict := true } csp

end CSP.L2S.MiniZinc
