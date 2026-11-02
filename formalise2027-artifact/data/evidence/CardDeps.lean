import LeanTypeSound
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let mut hits : Array Name := #[]
  let mut total := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanTypeSound).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    total := total + 1
    let mut visited : NameSet := {}
    let mut stack : Array Name := #[n]
    let mut found := false
    while h : stack.size > 0 do
      let c := stack.back
      stack := stack.pop
      if visited.contains c then continue
      visited := visited.insert c
      if c == `HOL4.CARD || c == `CARD then found := true; break
      match env.find? c with
      | some ci =>
        let mut s := ci.type.getUsedConstantsAsSet
        if let some v := ci.value? (allowOpaque := true) then s := s.union v.getUsedConstantsAsSet
        for d in s do
          unless visited.contains d do stack := stack.push d
      | none => pure ()
    if found then hits := hits.push n
  logInfo m!"theorems {total}; reaching CARD: {hits}"
