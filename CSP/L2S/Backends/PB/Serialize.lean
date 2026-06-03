import CSP.L2S.Backends.PB.Core

namespace CSP.L2S.PB

open Sat.PB (Constr Literal)

/-!
# PB backend — OPB serializer (untrusted)

Serializes a `Array Sat.PB.Constr` to the OPB text that RoundingSat consumes.
This is **outside the trust base**: a wrong serialization makes the external
solver prove the wrong formula, but PBLean's reflection checker then rejects the
returned certificate against the *Lean-side* constraint array (it never sees the
`.opb`), so a mismatch only ever causes a *failure to elaborate*, never an
unsound theorem.

Extracted from `Demo.lean` so it can be shared by the `csp_decide` command
(`Tactic.lean`), which calls these at elaboration time via `evalExpr`. The
format matches the external-toolchain recipe (1-based vars `x{i+1}`, `~` for
negation, `>=`, trailing ` ;`, RoundingSat's full header). -/

/-- Serialize one term (0-based Lean var `i` ↦ 1-based OPB `x{i+1}`). -/
def termToOPB : Nat × Literal → String
  | (a, .pos i) => s!"+{a} x{i + 1}"
  | (a, .neg i) => s!"+{a} ~x{i + 1}"

/-- Serialize one constraint to a line `+a x… … >= d ;`. -/
def constrToOPB (c : Constr) : String :=
  String.intercalate " " (c.terms.map termToOPB) ++ s!" >= {c.degree} ;"

/-- Serialize a constraint array to OPB text (with RoundingSat's header). -/
def toOPBString (cs : Array Constr) (numVars : Nat) : String :=
  let header := s!"* #variable= {numVars} #constraint= {cs.size} #equal= 0 intsize= 6"
  String.intercalate "\n" (header :: cs.toList.map constrToOPB) ++ "\n"

end CSP.L2S.PB
