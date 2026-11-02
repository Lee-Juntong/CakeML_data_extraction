import LeanTypeSound
open Lean Elab Command

/- For every theorem in LeanTypeSound modules, decide whether its statement
    (the theorem type) already depends on sorryAx, through the transitive
    closure of the constants that the statement mentions. Such a theorem cannot
    pass the transitive axiom audit, whatever its proof. -/
run_cmd do
  let env ← getEnv
  let mut lines : Array String := #[]
  let mut memo : Std.HashMap Name Bool := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanTypeSound).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    let mut tainted : Array Name := #[]
    for c in ci.type.getUsedConstants do
      let t ← match memo.get? c with
        | some b => pure b
        | none => do
          let axs ← liftCoreM <| Lean.collectAxioms c
          let b := axs.contains ``sorryAx
          pure b
      memo := memo.insert c t
      if t then tainted := tainted.push c
    lines := lines.push s!"{mod}\t{n}\t{!tainted.isEmpty}\t{",".intercalate (tainted.toList.map toString)}"
  IO.FS.writeFile "stmt_taint.tsv" ("\n".intercalate lines.toList)
  logInfo m!"wrote {lines.size} theorems"
