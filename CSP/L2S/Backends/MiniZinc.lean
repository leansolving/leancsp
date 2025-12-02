import CSP.L2S.Backend
import CSP.L2S.Core

namespace CSP.L2S.MiniZinc

open CSP.L2S

/-!
# MiniZinc Backend for L2M

Translates HomogeneousCSP to MiniZinc constraint programming language.

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
    (pattern : ConstraintPattern num_vars) : Except TranslatorError (List String) :=
  match pattern with
  | ConstraintPattern.alldifferent vars =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint alldifferent([{varList}]);"]

  | ConstraintPattern.alldifferentOffset vars offsets =>
      let terms := (vars.zip offsets).map fun (v, off) =>
        if off ≥ 0 then s!"x{v} + {off}" else s!"x{v} - {-off}"
      let termList := String.intercalate ", " terms
      .ok [s!"constraint alldifferent([{termList}]);"]

  | ConstraintPattern.increasing vars =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint increasing([{varList}]);"]

  | ConstraintPattern.sum vars op target =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      let opStr := relOpToMzn op
      .ok [s!"constraint sum([{varList}]) {opStr} {target};"]

  | ConstraintPattern.linear vars coeffs op target =>
      let terms := (vars.zip coeffs).map fun (v, c) => s!"({c})*x{v}"
      let exprStr := String.intercalate " + " terms
      let opStr := relOpToMzn op
      .ok [s!"constraint {exprStr} {opStr} {target};"]

  | ConstraintPattern.count vars value n =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint count([{varList}], {value}, {n});"]

  | ConstraintPattern.count_var vars value count_var =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint count([{varList}], {value}, x{count_var});"]

  | ConstraintPattern.element index array result =>
      let arrayStr := array.map toString |> String.intercalate ", "
      .ok [s!"constraint element(x{index}, [{arrayStr}], x{result});"]

  | ConstraintPattern.maximum vars maxVar =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint maximum(x{maxVar}, [{varList}]);"]

  | ConstraintPattern.minimum vars minVar =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint minimum(x{minVar}, [{varList}]);"]

  | ConstraintPattern.bound var lb ub =>
      .ok [s!"% Bound constraint x{var} ∈ [{lb}, {ub}] handled in variable declaration"]

  -- Binary comparison constraints
  | ConstraintPattern.eq var1 var2 =>
      .ok [s!"constraint x{var1} = x{var2};"]

  | ConstraintPattern.ne var1 var2 =>
      .ok [s!"constraint x{var1} != x{var2};"]

  | ConstraintPattern.lt var1 var2 =>
      .ok [s!"constraint x{var1} < x{var2};"]

  | ConstraintPattern.le var1 var2 =>
      .ok [s!"constraint x{var1} <= x{var2};"]

  | ConstraintPattern.gt var1 var2 =>
      .ok [s!"constraint x{var1} > x{var2};"]

  | ConstraintPattern.ge var1 var2 =>
      .ok [s!"constraint x{var1} >= x{var2};"]

  -- Unary comparison constraints
  | ConstraintPattern.eq_const var value =>
      .ok [s!"constraint x{var} = {value};"]

  | ConstraintPattern.ne_const var value =>
      .ok [s!"constraint x{var} != {value};"]

  | ConstraintPattern.lt_const var value =>
      .ok [s!"constraint x{var} < {value};"]

  | ConstraintPattern.le_const var value =>
      .ok [s!"constraint x{var} <= {value};"]

  | ConstraintPattern.gt_const var value =>
      .ok [s!"constraint x{var} > {value};"]

  | ConstraintPattern.ge_const var value =>
      .ok [s!"constraint x{var} >= {value};"]

  -- Logical/Disjunctive constraints
  | ConstraintPattern.schur_triple var1 var2 var3 =>
      .ok [s!"constraint x{var1} != x{var2} \\/ x{var1} != x{var3} \\/ x{var2} != x{var3};"]

  -- Absolute value constraints
  | ConstraintPattern.abs_diff_rel var1 var2 op target =>
      let opStr := relOpToMzn op
      .ok [s!"constraint abs(x{var1} - x{var2}) {opStr} {target};"]

  | ConstraintPattern.abs_diff_var var1 var2 result =>
      .ok [s!"constraint x{result} = abs(x{var1} - x{var2});"]

  -- Modulo constraints
  | ConstraintPattern.modulo var n k =>
      .ok [s!"constraint x{var} mod {n} = {k};"]

  -- Sliding window constraints
  | ConstraintPattern.sliding_sum vars window_size op target =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      let opStr := relOpToMzn op
      .ok [s!"constraint forall(i in 1..{vars.length - window_size + 1}) (sum([{varList}][i..i+{window_size}-1]) {opStr} {target});"]

  -- Boolean gate constraints
  | ConstraintPattern.not_gate in1 out =>
      .ok [s!"constraint x{out} = 1 - x{in1};"]

  | ConstraintPattern.and_gate in1 in2 out =>
      .ok [s!"constraint x{out} = min(x{in1}, x{in2});"]

  | ConstraintPattern.or_gate in1 in2 out =>
      .ok [s!"constraint x{out} = max(x{in1}, x{in2});"]

  | ConstraintPattern.xor_gate in1 in2 out =>
      .ok [s!"constraint (x{in1} + x{in2}) mod 2 = x{out};"]

  | ConstraintPattern.nand_gate in1 in2 out =>
      .ok [s!"constraint x{out} >= 1 - x{in1} /\\ x{out} >= 1 - x{in2} /\\ x{out} <= 2 - x{in1} - x{in2};"]

  | ConstraintPattern.nor_gate in1 in2 out =>
      .ok [s!"constraint x{out} <= 1 - x{in1} /\\ x{out} <= 1 - x{in2} /\\ x{out} >= 1 - x{in1} - x{in2};"]

  -- Multi-input logical operations
  | ConstraintPattern.and_all vars result =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint x{result} = min([{varList}]);"]

  | ConstraintPattern.or_all vars result =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint x{result} = max([{varList}]);"]

  | ConstraintPattern.xor_all vars result =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) mod 2 = x{result};"]

  -- Implication and equivalence
  | ConstraintPattern.implies premise conclusion =>
      .ok [s!"constraint x{conclusion} >= x{premise};"]

  | ConstraintPattern.iff var1 var2 =>
      .ok [s!"constraint x{var1} = x{var2};"]

  | ConstraintPattern.if_then var value next_var next_value =>
      .ok [s!"constraint (x{var} = {value}) -> (x{next_var} = {next_value});"]

  | ConstraintPattern.if_then_or var value next_var allowed_values =>
      let set_literal := "{" ++ String.intercalate ", " (allowed_values.map toString) ++ "}"
      .ok [s!"constraint (x{var} = {value}) -> (x{next_var} in {set_literal});"]

  -- Cardinality constraints
  | ConstraintPattern.at_least_k vars k =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) >= {k};"]

  | ConstraintPattern.at_most_k vars k =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) <= {k};"]

  | ConstraintPattern.exactly_k vars k =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      .ok [s!"constraint sum([{varList}]) = {k};"]

  -- Arithmetic constraints with variable targets
  | ConstraintPattern.product_rel_var vars op target_var =>
      let productTerms := vars.map (s!"x{·}") |> String.intercalate " * "
      let opStr := relOpToMzn op
      .ok [s!"constraint ({productTerms}) {opStr} x{target_var};"]

  | ConstraintPattern.linear_rel_var vars coeffs op target_var =>
      let terms := List.zip vars coeffs |>
        List.map (fun (v, c) =>
          if c = 1 then s!"x{v}"
          else if c = -1 then s!"(-x{v})"
          else s!"({c})*x{v}") |>
        String.intercalate " + "
      let opStr := relOpToMzn op
      .ok [s!"constraint ({terms}) {opStr} x{target_var};"]

  | ConstraintPattern.sum_rel_var vars op target_var =>
      let varList := vars.map (s!"x{·}") |> String.intercalate ", "
      let opStr := relOpToMzn op
      .ok [s!"constraint sum([{varList}]) {opStr} x{target_var};"]

  | ConstraintPattern.disjunctive tasks durs =>
      let task_vars := "[" ++ String.intercalate ", " (tasks.map (s!"x{·}")) ++ "]"
      let dur_vals := "[" ++ String.intercalate ", " (durs.map toString) ++ "]"
      .ok [s!"constraint disjunctive({task_vars}, {dur_vals});"]

  | ConstraintPattern.unknown _ scope =>
      .error ⟨s!"Unknown constraint on variables: {scope}"⟩

-- ============================================================================
-- Include Generation
-- ============================================================================

/-- Get required MiniZinc include statements for the constraints -/
def getRequiredIncludes (csp : HomogeneousCSP) : List String :=
  let patterns := csp.constraints.map (·.pattern)
  let includes := patterns.foldl (fun acc p =>
    match p with
    | ConstraintPattern.alldifferent _ => "alldifferent" :: acc
    | ConstraintPattern.alldifferentOffset _ _ => "alldifferent" :: acc
    | ConstraintPattern.increasing _ => "globals" :: acc
    | ConstraintPattern.count _ _ _ => "count" :: acc
    | ConstraintPattern.count_var _ _ _ => "count" :: acc
    | ConstraintPattern.element _ _ _ => "element" :: acc
    | ConstraintPattern.maximum _ _ => "maximum" :: acc
    | ConstraintPattern.minimum _ _ => "minimum" :: acc
    | ConstraintPattern.disjunctive _ _ => "disjunctive" :: acc
    | ConstraintPattern.bound _ _ _ => acc
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
    | ConstraintPattern.bound _ _ _ => true
    | _ => false

-- ============================================================================
-- Public API
-- ============================================================================

/-- Convenience wrapper (backward compatibility) -/
def translateToMiniZinc (csp : HomogeneousCSP) : String :=
  match translateWith miniZincBackend default csp with
  | .ok s => s
  | .error e => s!"% Error: {e.msg}"

/-- Convenience wrapper with options -/
def translateToMiniZincStrict (csp : HomogeneousCSP) : Except TranslatorError String :=
  translateWith miniZincBackend { strict := true } csp

end CSP.L2S.MiniZinc
