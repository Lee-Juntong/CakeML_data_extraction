/-
Observability of the Table VII defects in the Direct endpoint (branch proof2-direct).
Run from r2\direct\lean_type_sound:  lake env lean <this file>
Reads the 269 canonical theorems (module, name) of de795c9f6 from canon.tsv next to this file.

(a) full closure of semantics_type_sound: types and values of every reached constant (proofs included),
    plus the constructors of every reached inductive.
(b) statement closure of each canonical theorem: the theorem TYPE, then transitively types of everything,
    values of definitions/opaques (not of theorems), and constructors of inductives.
-/
import LeanTypeSound
open Lean Elab Command

def obsTargets : List (String × List String) := [
  ("FV", ["FV"]), ("FV_defs", ["FV_defs"]),
  ("type_v", ["type_v"]), ("type_v.conv_some", ["type_v.conv_some"]), ("type_v.conv_none", ["type_v.conv_none"]),
  ("type_v.closure", ["type_v.closure"]), ("type_v.recclosure", ["type_v.recclosure"]),
  ("alist_to_fmap", ["Finmap.alist_to_fmap"]), ("FUPDATE_LIST", ["Finmap.FUPDATE_LIST"]),
  ("nsAll2", ["nsAll2"]), ("nsSub", ["nsSub"]),
  ("Mllist.sort", ["sort"]), ("strsub", ["strsub"]),
  ("BEq v instance", ["instBEqV"]), ("BEq sem_env instance", ["instBEqSem_env"]),
  ("v_beq", ["v_beq"]), ("sem_env_beq", ["sem_env_beq"]),
  ("Sptree.lookup", ["Sptree.lookup"]), ("CARD", ["CARD"]),
  ("Sptree.toList", ["Sptree.toList"]), ("Sptree.toAList", ["Sptree.toAList"]),
  ("word_lsl_8", ["word_lsl_8"]), ("word_lsr_8", ["word_lsr_8"]), ("word_asr_8", ["word_asr_8"]),
  ("word_lsl_64", ["word_lsl_64"]), ("word_lsr_64", ["word_lsr_64"]), ("word_asr_64", ["word_asr_64"]),
  ("fp64_mul_add", ["fp64_mul_add"]),
  ("shift8_lookup", ["shift8_lookup"]), ("shift64_lookup", ["shift64_lookup"]),
  ("shift_lookup_8", ["shift_lookup_8"]), ("shift_lookup_64", ["shift_lookup_64"]),
  ("do_app", ["do_app"]),
  ("do_app_cases", ["do_app_cases"]), ("type_op_cases_thm", ["type_op_cases_thm"])]

def isLTS (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]!).toString.startsWith "LeanTypeSound"
  | none => false

/-- All LeanTypeSound constants (computed once). -/
def ltsConsts (env : Environment) : Array Name :=
  env.constants.map₁.fold (init := #[]) fun acc n _ => if isLTS env n then acc.push n else acc

/-- LeanTypeSound constants whose name ends with the given dotted suffix (component-wise). -/
def resolveSuffix (lts : Array Name) (suf : String) : Array Name := Id.run do
  let comps := (suf.splitOn ".").reverse
  let mut out := #[]
  for n in lts do
    let cs := n.components.reverse.map (·.toString)
    if cs.length ≥ comps.length && cs.take comps.length == comps then out := out.push n
  return out

def closureOf (env : Environment) (roots : Array Name) (proofs : Bool) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack := roots
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    unless isLTS env c do continue
    let some ci := env.find? c | continue
    let mut s := ci.type.getUsedConstantsAsSet
    match ci with
    | .thmInfo t => if proofs then s := s.union t.value.getUsedConstantsAsSet
    | .defnInfo d => s := s.union d.value.getUsedConstantsAsSet
    | .opaqueInfo o => s := s.union o.value.getUsedConstantsAsSet
    | .inductInfo i => for k in i.ctors do s := s.insert k
    | _ => pure ()
    for d in s do
      unless visited.contains d do stack := stack.push d
  return visited

run_cmd do
  let env ← getEnv
  let lts := ltsConsts env
  -- resolve targets
  let mut tgts : Array (String × Array Name) := #[]
  for (label, sufs) in obsTargets do
    let mut ns := #[]
    for s in sufs do ns := ns ++ resolveSuffix lts s
    -- `sort` must be the Mllist one; `lookup` the Sptree one
    if label == "Mllist.sort" then
      ns := ns.filter fun n => match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i.toNat]!).toString == "LeanTypeSound.Mllist" && n.components.length ≤ 2
        | none => false
    tgts := tgts.push (label, ns)
  -- (a)
  let full := closureOf env #[`semantics_type_sound] true
  -- canonical theorems
  let path : System.FilePath := "E:/NUS/mcomp/Dissertation/publication/formalise2027/paper/evidence/canon.tsv"
  let lines := (← IO.FS.lines path).filter (· ≠ "")
  let mut canon : Array Name := #[]
  let mut missing : Array String := #[]
  let mut moved := 0
  for l in lines do
    let parts := l.splitOn "\t"
    let modS := parts[0]!
    let nm := parts[1]!
    let thms := (resolveSuffix lts nm).filter fun n =>
      (env.find? n).any (fun ci => ci matches .thmInfo _) && !n.isInternal
    let inMod := thms.filter fun n => match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!).toString == modS
      | none => false
    -- the Direct branch split TypeSound.lean into TypeSoundCore/TypeSoundExp/TypeSound; fall back to a unique match
    let cands := if inMod.size > 0 then inMod else if thms.size == 1 then thms else #[]
    if inMod.size == 0 && thms.size == 1 then moved := moved + 1
    match cands[0]? with
    | some n => canon := canon.push n
    | none => missing := missing.push l
  logInfo m!"canonical theorems resolved: {canon.size} ({moved} found in another module), unresolved: {missing}"
  -- (b)
  let stmtClosures := canon.map fun t => (t, closureOf env #[t] false)
  let mut rows : Array String := #[]
  for (label, ns) in tgts do
    let inFull := ns.any full.contains
    let reaching := stmtClosures.filter fun (_, c) => ns.any c.contains
    let directT := canon.filter fun t => match env.find? t with
      | some ci => ns.any ci.type.getUsedConstantsAsSet.contains
      | none => false
    let ex := (reaching.toList.take 4).map (·.1)
    let users := lts.filter fun c => match env.find? c with
      | some (.defnInfo d) => !c.isInternal && ns.any d.value.getUsedConstantsAsSet.contains
      | _ => false
    rows := rows.push s!"{label} | {ns.toList} | closure(semantics_type_sound)={inFull} | stmt-reach={reaching.size}/{canon.size} | in-type-directly={directT.size} | e.g. {ex} | def users={users.toList.take 8}"
  logInfo m!"{String.intercalate "\n" rows.toList}"
  -- proofs in the full closure that use do_app_cases / type_op_cases_thm
  for nm in [`do_app_cases, `type_op_cases_thm] do
    let users := full.toList.filter fun c => match env.find? c with
      | some (.thmInfo t) => t.value.getUsedConstantsAsSet.contains nm
      | some (.defnInfo d) => d.value.getUsedConstantsAsSet.contains nm
      | _ => false
    let allUsers := lts.filter fun c => match env.find? c with
      | some (.thmInfo t) => t.value.getUsedConstantsAsSet.contains nm
      | _ => false
    logInfo m!"{nm}: in closure={full.contains nm}; closure users={users}; all users in env={allUsers}"
