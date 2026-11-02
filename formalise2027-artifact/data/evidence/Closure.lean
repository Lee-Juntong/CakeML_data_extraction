import LeanTypeSound
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let targets : List String := ["getOpClass","every_exp","list_result","evaluate","evaluate_decs","call_FFI","CARD","roundTiesToEven","locn_colupdate","nsMap","nsSub_compute","list_type_num","store_assign","pmatch_list","find_recfun","do_eq_list","concrete_v_list","check_freevars","check_freevars_ast","check_type_names","is_value","tlookup_bij_suff","tlookup_bij_iff","CARD_IMAGE_ID_BIJ","CARD_eq_of_nodup"]
  for root in [`semantics_type_sound, `decs_type_sound] do
    let some _ := env.find? root | logInfo m!"missing {root}"
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
    let mut hits : Array String := #[]
    for t in targets do
      let found := visited.toList.any fun n => n.toString == t || n.toString.endsWith ("." ++ t)
      hits := hits.push s!"{t}={found}"
    logInfo m!"{root}: closure size {visited.size}; {hits}"
