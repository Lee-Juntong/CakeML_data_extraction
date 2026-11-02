import LeanTypeSound
open Lean Meta Elab Command

/- A statement is vacuous when, after its binders and hypotheses, its conclusion
   is True, or an equation or equivalence whose two sides agree at reducible
   transparency (for example `P ↔ P`). Conjunctions are vacuous when every
   conjunct is. -/
partial def vacuousBody (b : Expr) : MetaM Bool := do
  let b ← whnfR b
  if b.isConstOf ``True then return true
  if let some (l, r) := b.and? then return (← vacuousConcl l) && (← vacuousConcl r)
  if let some (l, r) := b.iff? then return ← withReducible (isDefEq l r)
  if let some (_, l, r) := b.eq? then return ← withReducible (isDefEq l r)
  return false
where vacuousConcl (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ body => vacuousBody body

run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`LeanTypeSound).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    let v ← liftTermElabM <| forallTelescopeReducing ci.type fun _ body => vacuousBody body
    if v then out := out.push s!"{mod}\t{n}"
  IO.FS.writeFile "vacuous.tsv" ("\n".intercalate out.toList)
  logInfo m!"{out.size} vacuous statements: {out}"
