import LeanTypeSound
open Lean Elab Command

/- For every theorem in LeanTypeSound modules: its axioms, and the set of
    "sorry roots": transitively used constants whose own type or value mentions sorryAx. -/
partial def usedConsts (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | some ci =>
    let s := ci.type.getUsedConstantsAsSet
    match ci.value? (allowOpaque := true) with
    | some v => s.union v.getUsedConstantsAsSet
    | none => s
  | none => {}

run_cmd do
  let env ← getEnv
  -- direct sorry mentions
  let mut lines : Array String := #[]
  let mut memo : Std.HashMap Name NameSet := {}
  let isDirectSorry := fun (n : Name) => (usedConsts env n).contains ``sorryAx
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanTypeSound).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    -- transitive closure restricted to LeanTypeSound constants, collecting sorry roots
    let mut visited : NameSet := {}
    let mut stack : Array Name := #[n]
    let mut roots : Array Name := #[]
    while h : stack.size > 0 do
      let c := stack.back
      stack := stack.pop
      if visited.contains c then continue
      visited := visited.insert c
      let us := usedConsts env c
      if us.contains ``sorryAx then roots := roots.push c
      for u in us do
        unless visited.contains u do
          match env.getModuleIdxFor? u with
          | some j =>
            if (`LeanTypeSound).isPrefixOf env.header.moduleNames[j.toNat]! then stack := stack.push u
          | none => pure ()
    let axs ← liftCoreM <| Lean.collectAxioms n
    let kinds := roots.map fun r =>
      match env.find? r with
      | some (.thmInfo _) => s!"thm:{r}"
      | some (.defnInfo _) => s!"def:{r}"
      | some (.opaqueInfo _) => s!"opaque:{r}"
      | some (.inductInfo _) => s!"ind:{r}"
      | _ => s!"other:{r}"
    lines := lines.push s!"{mod}\t{n}\t{",".intercalate (axs.toList.map toString)}\t{";".intercalate kinds.toList}"
  IO.FS.writeFile "axioms.tsv" ("\n".intercalate lines.toList)
  logInfo m!"wrote {lines.size} theorems"
