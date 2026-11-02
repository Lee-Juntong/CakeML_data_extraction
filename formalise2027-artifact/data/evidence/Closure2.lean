import LeanTypeSound
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let root := `semantics_type_sound
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    match env.find? c with
    | some ci =>
      let mut s := ci.type.getUsedConstantsAsSet
      if let some v := ci.value? (allowOpaque := true) then s := s.union v.getUsedConstantsAsSet
      for d in s do
        unless visited.contains d do stack := stack.push d
    | none => pure ()
  -- count LeanTypeSound constants by module and kind, excluding internal names
  let mut counts : Std.HashMap String Nat := {}
  let mut prelude : Array String := #[]
  for n in visited.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := (env.header.moduleNames[idx.toNat]!).toString
    unless mod.startsWith "LeanTypeSound" do continue
    let some ci := env.find? n | continue
    let kind := match ci with
      | .thmInfo _ => "thm" | .defnInfo _ => "def" | .inductInfo _ => "ind" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom" | _ => "other"
    if kind == "ctor" || kind == "rec" then continue
    let key := s!"{mod}:{kind}"
    counts := counts.insert key (counts.getD key 0 + 1)
    if mod == "LeanTypeSound.HOL4Prelude" && (kind == "def" || kind == "ind" || kind == "opaque") then prelude := prelude.push n.toString
  let lines := counts.toList.map (fun (k, v) => s!"{k}={v}")
  logInfo m!"{lines}"
  logInfo m!"prelude defs/types in closure ({prelude.size}): {prelude.qsort (· < ·)}"
