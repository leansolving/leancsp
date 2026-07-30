import VeriPB.Tactic.Sat.Reflect

open Sat.PB

/-- Whitespace-tokenize (small constraint files, so a simple char fold is fine). -/
def tokenize (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  let mut cur : String := ""
  for c in s.toList do
    if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
      if cur ≠ "" then out := out.push cur; cur := ""
    else
      cur := cur.push c
  if cur ≠ "" then out := out.push cur
  return out

/-- Parse the serialized constraint file written by lib/lean_dump.py:
    token 0 = number of constraints N; then, per constraint,
    `degree numTerms (coeff sign var)*` with sign 0 = positive literal, 1 = negated. -/
def parseConstrs (s : String) : Array Constr := Id.run do
  let toks := tokenize s
  let n := toks[0]!.toNat!
  let mut i := 1
  let mut cs : Array Constr := Array.mkEmpty n
  for _ in [0:n] do
    let degree := toks[i]!.toNat!
    let nt := toks[i + 1]!.toNat!
    i := i + 2
    let mut terms : Array (Nat × Literal) := Array.mkEmpty nt
    for _ in [0:nt] do
      let lit := if toks[i + 1]!.toNat! == 0 then Literal.pos toks[i + 2]!.toNat!
                 else Literal.neg toks[i + 2]!.toNat!
      terms := terms.push (toks[i]!.toNat!, lit)
      i := i + 3
    cs := cs.push { terms := terms.toList, degree := degree }
  return cs

/-- `checkbench <constrs-file> <numVars> <proof-file>`: time ONE compiled `checkProofBool`.
    The constraint array is parsed and the proof read *before* the clock; the result is forced
    (an unbalanced `if`) *before* the second reading. This is native code — the exact function
    `Lean.ofReduceBool` reduces in the committed pipeline. -/
def main (args : List String) : IO Unit := do
  match args with
  | [constrsFile, numVarsStr, proofFile] =>
    let cs := parseConstrs (← IO.FS.readFile constrsFile)
    let _ := cs.size
    let proof ← IO.FS.readFile proofFile
    let _ := proof.length
    let t0 ← IO.monoNanosNow
    let ok := VeriPB.Reflect.checkProofBool cs numVarsStr.toNat! proof
    if ok then pure () else IO.eprintln "checkProofBool returned false"
    let t1 ← IO.monoNanosNow
    IO.println s!"NATIVE {t1 - t0} OK {ok} NCONS {cs.size}"
  | _ => IO.eprintln "usage: checkbench <constrs-file> <numVars> <proof-file>"
