import Mathlib.Tactic.Sat.FromLRAT

/-!
# Bounded-memory LRAT import

Mathlib's `lrat_proof` builds one proof expression for the complete trace before
adding it to the environment.  This module provides commands for checking a
large trace in several Lean modules.  The input clauses used by the LRAT trace
are installed in one balanced opaque bundle, and every derived clause is
installed as a separate opaque theorem.  A later chunk therefore refers to
compact constants and projections instead of retaining expanded proof
expressions.

The chunks must form an unbroken chain of imports and use the same CNF, LRAT,
context name, and clause-prefix name.  The half-open step interval is counted in
parsed LRAT records, including deletion records.
-/

-- Source strings are read as data. Every installed theorem is kernel checked.
-- No evaluator is used to turn a computation into a proposition.
open Lean
open Mathlib.Tactic.Sat

namespace MathIsEasy.Tactic.Sat.LRATStream

private meta def parseCNF (cnf : String) : MetaM (Nat × Array (Array Int)) := do
  let .success _ parsed := Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if parsed.2.isEmpty then
    throwError "empty CNF"
  return parsed

private meta def parseProof (lrat : String) : MetaM (Array LRATStep) := do
  let .success _ steps := Parser.parseLRAT ⟨_, lrat.startPos⟩
    | throwError "parse LRAT failed"
  return steps

private def clauseDeclName (declPrefix : Name) (id : Nat) : Name :=
  Name.str declPrefix s!"clause_{id}"

private def inputBundleDeclName (declPrefix : Name) : Name :=
  Name.str declPrefix "inputClauses"

private meta def referencedInputIds (steps : Array LRATStep) (maxId : Nat) :
    Std.HashMap Nat Unit := Id.run do
  let mut referenced : Std.HashMap Nat Unit := {}
  for step in steps do
    match step with
    | .del _ => pure ()
    | .add _ _ proofTrace =>
      for signedId in proofTrace do
        let id := signedId.natAbs
        if id > 0 && id <= maxId then
          referenced := referenced.insert id ()
  return referenced

private meta def selectedInputClauses (arr : Array (Array Int)) (ctx ctxValue : Expr)
    (steps : Array LRATStep) : Array (Nat × Mathlib.Tactic.Sat.Clause) := Id.run do
  let subsumesSelf := mkApp (mkConst ``_root_.Sat.Fmla.subsumes_self) ctx
  let allClauses := (buildClauses arr ctx 0 arr.size ctxValue subsumesSelf default).2
  let referenced := referencedInputIds steps arr.size
  let mut selected := #[]
  for offset in [:arr.size] do
    let id := offset + 1
    if referenced.contains id then
      let some clause := allClauses[id]?
        | panic! s!"missing input clause {id}"
      selected := selected.push (id, clause)
  return selected

private meta partial def buildInputBundle
    (clauses : Array (Nat × Mathlib.Tactic.Sat.Clause)) (ctx : Expr) (start stop : Nat) :
    Expr × Expr :=
  match stop - start with
  | 0 => panic! "empty input-clause bundle"
  | 1 => match clauses[start]? with
    | none => panic! s!"missing selected input clause at offset {start}"
    | some (_, clause) =>
      (mkApp2 (mkConst ``_root_.Sat.Fmla.proof) ctx clause.expr, clause.proof)
  | len =>
    let mid := start + len / 2
    let (leftType, leftProof) := buildInputBundle clauses ctx start mid
    let (rightType, rightProof) := buildInputBundle clauses ctx mid stop
    (mkApp2 (mkConst ``And) leftType rightType,
      mkApp4 (mkConst ``And.intro) leftType rightType leftProof rightProof)

private meta partial def installInputBundle
    (clauses : Array (Nat × Mathlib.Tactic.Sat.Clause)) (start stop : Nat) (proof : Expr)
    (db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause) :
    Std.HashMap Nat Mathlib.Tactic.Sat.Clause :=
  match stop - start with
  | 0 => panic! "empty input-clause bundle"
  | 1 => match clauses[start]? with
    | none => panic! s!"missing selected input clause at offset {start}"
    | some (id, clause) => db.insert id { clause with proof }
  | len =>
    let mid := start + len / 2
    let db := installInputBundle clauses start mid (mkProj ``And 0 proof) db
    installInputBundle clauses mid stop (mkProj ``And 1 proof) db

private meta def initialDB (arr : Array (Array Int)) (ctx ctxValue : Expr)
    (steps : Array LRATStep) (declPrefix : Name) :
    Std.HashMap Nat Mathlib.Tactic.Sat.Clause :=
  let clauses := selectedInputClauses arr ctx ctxValue steps
  installInputBundle clauses 0 clauses.size (mkConst (inputBundleDeclName declPrefix)) default

private meta def replayMetadata (steps : Array LRATStep) (stop : Nat)
    (declPrefix : Name) (db0 : Std.HashMap Nat Mathlib.Tactic.Sat.Clause) :
    MetaM (Std.HashMap Nat Mathlib.Tactic.Sat.Clause) := do
  let mut db := db0
  let mut index := 0
  while index < stop do
    if h : index < steps.size then
      match steps[index] with
      | .del ids => db := ids.foldl (·.erase ·) db
      | .add id lits _ =>
        if lits.isEmpty then
          throwError "empty clause occurs before this chunk at LRAT step {index}"
        db := db.insert id {
          lits
          expr := buildClause lits
          proof := mkConst (clauseDeclName declPrefix id)
        }
      index := index + 1
    else
      throwError "chunk start {stop} exceeds LRAT length {steps.size}"
  return db

/-- Add the shared CNF formula under `name`.  Put this command in the base module. -/
elab "lrat_stream_context " n:ident ppSpace cnfTerm:str : command => do
  let name := (← getCurrNamespace) ++ n.getId
  Lean.Elab.Command.liftTermElabM do
    let cnf ← IO.FS.readFile cnfTerm.getString
    let (_, arr) ← parseCNF cnf
    addDecl <| Declaration.defnDecl {
      name
      levelParams := []
      type := mkConst ``_root_.Sat.Fmla
      value := buildConj arr 0 arr.size
      hints := .regular 0
      safety := .safe
    }

/--
Install one balanced opaque theorem containing every input-clause proof that the
LRAT trace references.  Put this command after `lrat_stream_context` in the base
module shared by all chunks.
-/
elab "lrat_stream_inputs " ctxId:ident ppSpace prefixId:ident ppSpace
    cnfTerm:str ppSpace lratTerm:str : command => do
  let ns ← getCurrNamespace
  let ctxName := ns ++ ctxId.getId
  let declPrefix := ns ++ prefixId.getId
  Lean.Elab.Command.liftTermElabM do
    let cnf ← IO.FS.readFile cnfTerm.getString
    let lrat ← IO.FS.readFile lratTerm.getString
    let (_, arr) ← parseCNF cnf
    let steps ← parseProof lrat
    let ctxValue := buildConj arr 0 arr.size
    let ctx := mkConst ctxName
    let clauses := selectedInputClauses arr ctx ctxValue steps
    if clauses.isEmpty then
      throwError "LRAT trace references no input clauses"
    let (bundleType, bundleProof) := buildInputBundle clauses ctx 0 clauses.size
    addDecl <| Declaration.thmDecl {
      name := inputBundleDeclName declPrefix
      levelParams := []
      type := bundleType
      value := bundleProof
    }

/--
Check and install the LRAT records in the half-open interval `[start, stop)`.

All records before `start` are replayed only as clause metadata; their proof
fields refer to opaque theorem constants produced by preceding imported chunks.
-/
elab "lrat_stream_chunk " ctxId:ident ppSpace prefixId:ident ppSpace
    start:num ppSpace stop:num ppSpace cnfTerm:str ppSpace lratTerm:str : command => do
  let ns ← getCurrNamespace
  let ctxName := ns ++ ctxId.getId
  let declPrefix := ns ++ prefixId.getId
  let start := start.getNat
  let stop := stop.getNat
  if stop < start then
    throwError "invalid LRAT chunk [{start}, {stop})"
  Lean.Elab.Command.liftTermElabM do
    let cnf ← IO.FS.readFile cnfTerm.getString
    let lrat ← IO.FS.readFile lratTerm.getString
    let (_, arr) ← parseCNF cnf
    let steps ← parseProof lrat
    if stop > steps.size then
      throwError "chunk stop {stop} exceeds LRAT length {steps.size}"
    let ctxValue := buildConj arr 0 arr.size
    let ctx := mkConst ctxName
    let mut db ← replayMetadata steps start declPrefix
      (initialDB arr ctx ctxValue steps declPrefix)
    let mut index := start
    let mut additions : Nat := 0
    while index < stop do
      let some step := steps[index]?
        | throwError "missing LRAT step {index}"
      match step with
      | .del ids => db := ids.foldl (·.erase ·) db
      | .add id lits proofTrace =>
        let clauseExpr := buildClause lits
        let proof ← match buildProofStep db lits proofTrace ctx clauseExpr with
          | .ok proof => pure proof
          | .error message => throwError "LRAT step {index}, clause {id}: {message}"
        let declName := clauseDeclName declPrefix id
        addDecl <| Declaration.thmDecl {
          name := declName
          levelParams := []
          type := mkApp2 (mkConst ``_root_.Sat.Fmla.proof) ctx clauseExpr
          value := proof
        }
        if !lits.isEmpty then
          db := db.insert id { lits, expr := clauseExpr, proof := mkConst declName }
        additions := additions + 1
        if additions % 100 == 0 then
          liftM (IO.eprintln s!"LRAT_STREAM_PROGRESS additions={additions} step={index + 1}/{stop}")
        if additions % 1000 == 0 then
          logInfo m!"LRAT chunk progress: {additions} additions, source step {index + 1}/{stop}"
      index := index + 1

end MathIsEasy.Tactic.Sat.LRATStream
