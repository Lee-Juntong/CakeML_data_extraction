import LeanTypeSound
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanTypeSound).isPrefixOf mod do continue
    let vs := match ci.value? (allowOpaque := true) with | some v => v.getUsedConstantsAsSet | none => {}
    if (ci.type.getUsedConstantsAsSet.union vs).contains ``sorryAx then
      let k := match ci with | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | _ => "other"
      out := out.push s!"{mod}\t{k}\t{n}"
  IO.FS.writeFile "defsorry.tsv" ("\n".intercalate out.toList)
