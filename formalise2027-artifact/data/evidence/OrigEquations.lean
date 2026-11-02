import LeanTypeSound

/-!
# The rewritten (terminating) definitions satisfy the original equations

Each theorem below states that a definition rewritten for termination
satisfies the defining equation(s) of the original definition at commit
4841f993e, with recursive calls referring to the new constant.
-/

open HOL4

theorem all_attach_comp {α : Type} (l : List α) (g : α → Bool) :
    (l.attach.all fun x => g x.1) = l.all g := by
  simp

-- ============================================================
-- every_exp (Ast.lean)
-- ============================================================

theorem every_exp_orig_eqn (p : exp → Bool) (e : exp) :
    every_exp p e =
      match e with
      | .Raise e => p (.Raise e) && every_exp p e
      | .Handle e pes =>
        p (.Handle e pes) && every_exp p e && pes.all fun (_, e') => every_exp p e'
      | .Lit l => p (.Lit l)
      | .Con cn es => p (.Con cn es) && es.all (every_exp p)
      | .Var v => p (.Var v)
      | .Fun x e => p (.Fun x e) && every_exp p e
      | .App o es => p (.App o es) && es.all (every_exp p)
      | .Log l e1 e2 => p (.Log l e1 e2) && every_exp p e1 && every_exp p e2
      | .If e1 e2 e3 => p (.If e1 e2 e3) && every_exp p e1 && every_exp p e2 && every_exp p e3
      | .Mat e pes =>
        p (.Mat e pes) && every_exp p e && pes.all fun (_, e') => every_exp p e'
      | .Let x e1 e2 => p (.Let x e1 e2) && every_exp p e1 && every_exp p e2
      | .Tannot e a => p (.Tannot e a) && every_exp p e
      | .Lannot e a => p (.Lannot e a) && every_exp p e
      | .Letrec funs e =>
        p (.Letrec funs e) && every_exp p e && funs.all fun (_, _, e') => every_exp p e' := by
  rw [every_exp.eq_def]
  cases e <;> simp
  all_goals first
    | (congr 1; exact all_attach_comp _ (fun (y : pat × exp) => every_exp p y.2))
    | (congr 1; exact all_attach_comp _ (fun (y : varN × varN × exp) => every_exp p y.2.2))

-- ============================================================
-- TypeSystem.lean
-- ============================================================

theorem check_freevars_orig_eqn (n : Nat) (ls : List mlstring) (t : sem_t) :
    check_freevars n ls t =
      match n, ls, t with
      | _, tvs, .Tvar tv => tvs.any (· == tv)
      | dbmax, tvs, .Tapp ts _ => ts.all (check_freevars dbmax tvs)
      | dbmax, _, .Tvar_db n => n < dbmax := by
  rw [check_freevars.eq_def]
  cases t <;> simp

theorem check_freevars_ast_orig_eqn (ls : List mlstring) (t : ast_t) :
    check_freevars_ast ls t =
      match ls, t with
      | tvs, .Atvar tv => tvs.any (· == tv)
      | tvs, .Attup ts => ts.all (check_freevars_ast tvs)
      | tvs, .Atfun t1 t2 => check_freevars_ast tvs t1 && check_freevars_ast tvs t2
      | tvs, .Atapp ts _ => ts.all (check_freevars_ast tvs) := by
  rw [check_freevars_ast.eq_def]
  cases t <;> simp

theorem check_type_names_orig_eqn (tenvT : tenv_abbrev) (t : ast_t) :
    check_type_names tenvT t =
      match t with
      | .Atvar _ => true
      | .Attup ts => ts.all (check_type_names tenvT)
      | .Atfun t1 t2 => check_type_names tenvT t1 && check_type_names tenvT t2
      | .Atapp ts tn =>
        (match nsLookup tenvT tn with
         | some (tvs, _) => tvs.length == ts.length
         | none => false) &&
        ts.all (check_type_names tenvT) := by
  rw [check_type_names.eq_def]
  cases t <;> simp <;> rfl

theorem is_value_orig_eqn (e : exp) :
    is_value e =
      match e with
      | .Lit _ => true
      | .Con _ es => es.all is_value
      | .Var _ => true
      | .Fun _ _ => true
      | .Tannot e _ => is_value e
      | .Lannot e _ => is_value e
      | _ => false := by
  rw [is_value.eq_def]
  cases e <;> simp

-- ============================================================
-- SemanticPrimitives.lean (bodies unchanged; only the sorry'd
-- termination annotations were removed)
-- ============================================================

theorem pmatch_orig_eqn (envC : env_ctor) (s : store v) (p : pat) (w : v) (env : alist varN v) :
    pmatch envC s p w env =
      match p, w, env with
      | .Pany, _, env => .Match env
      | .Pvar x, v', env => .Match ((x, v') :: env)
      | .Plit l, .Litv l', env =>
        if l == l' then .Match env
        else if lit_same_type l l' then .No_match
        else .Match_type_error
      | .Pcon (some n) ps, .Conv (some stamp') vs, env =>
        match nsLookup envC n with
        | none => .Match_type_error
        | some (l, stmp) =>
          if same_type stmp stamp' && ps.length == l then
            if same_ctor stmp stamp' then
              if vs.length == l then pmatch_list envC s ps vs env
              else .Match_type_error
            else .No_match
          else .Match_type_error
      | .Pcon none ps, .Conv none vs, env =>
        if ps.length == vs.length then pmatch_list envC s ps vs env
        else .Match_type_error
      | .Pref p, .Loc _ lnum, env =>
        match store_lookup lnum s with
        | none => .Match_type_error
        | some (.Refv v') => pmatch envC s p v' env
        | some _ => .Match_type_error
      | .Pas p i, v', env => pmatch envC s p v' ((i, v') :: env)
      | .Ptannot p _, v', env => pmatch envC s p v' env
      | _, _, _ => .Match_type_error := by
  rw [pmatch.eq_def]; rfl

theorem pmatch_list_orig_eqn (envC : env_ctor) (s : store v) (ps : List pat) (vs : List v)
    (env : alist varN v) :
    pmatch_list envC s ps vs env =
      match ps, vs, env with
      | [], [], env => .Match env
      | p :: ps, v' :: vs, env =>
        match pmatch envC s p v' env with
        | .No_match =>
          match pmatch_list envC s ps vs env with
          | .No_match => .No_match
          | .Match_type_error => .Match_type_error
          | .Match _ => .No_match
        | .Match_type_error => .Match_type_error
        | .Match env' => pmatch_list envC s ps vs env'
      | _, _, _ => .Match_type_error := by
  rw [pmatch_list.eq_def]; rfl

theorem do_eq_orig_eqn (a b : v) :
    do_eq a b =
      match a, b with
      | .Litv l1, .Litv l2 =>
        if lit_same_type l1 l2 then .Eq_val (l1 == l2) else .Eq_type_error
      | .Loc b1 l1, .Loc b2 l2 =>
        if b1 && b2 then .Eq_val (l1 == l2) else .Eq_type_error
      | .Conv cn1 vs1, .Conv cn2 vs2 =>
        if cn1 == cn2 && vs1.length == vs2.length then do_eq_list vs1 vs2
        else if ctor_same_type cn1 cn2 then .Eq_val false
        else .Eq_type_error
      | .Vectorv vs1, .Vectorv vs2 =>
        if vs1.length == vs2.length then do_eq_list vs1 vs2 else .Eq_val false
      | .Closure _ _ _, .Closure _ _ _ => .Eq_val true
      | .Closure _ _ _, .Recclosure _ _ _ => .Eq_val true
      | .Recclosure _ _ _, .Closure _ _ _ => .Eq_val true
      | .Recclosure _ _ _, .Recclosure _ _ _ => .Eq_val true
      | .Env _ (gen1, id1), .Env _ (gen2, id2) => .Eq_val (gen1 == gen2 && id1 == id2)
      | _, _ => .Eq_type_error := by
  rw [do_eq.eq_def]; rfl

theorem do_eq_list_orig_eqn (a b : List v) :
    do_eq_list a b =
      match a, b with
      | [], [] => .Eq_val true
      | v1 :: vs1, v2 :: vs2 =>
        match do_eq v1 v2 with
        | .Eq_val r => if !r then .Eq_val false else do_eq_list vs1 vs2
        | .Eq_type_error => .Eq_type_error
      | _, _ => .Eq_val false := by
  rw [do_eq_list.eq_def]; rfl

theorem concrete_v_orig_eqn (a : v) :
    concrete_v a =
      match a with
      | .Loc _ _ => true
      | .Litv _ => true
      | .Conv _ vs => concrete_v_list vs
      | .Vectorv vs => concrete_v_list vs
      | _ => false := by
  rw [concrete_v.eq_def]; rfl

theorem concrete_v_list_orig_eqn (a : List v) :
    concrete_v_list a =
      match a with
      | [] => true
      | val_ :: vs => concrete_v val_ && concrete_v_list vs := by
  rw [concrete_v_list.eq_def]; rfl

-- ============================================================
-- nsMap (Namespace.lean)
-- ============================================================

theorem nsMap_orig_eqn {m n v w : Type} (f : v → w) (vals : List (n × v))
    (mods : List (m × «namespace» m n v)) :
    nsMap f (.Bind vals mods) =
      .Bind (vals.map fun (name, x) => (name, f x))
            (mods.map fun (mn, e) => (mn, nsMap f e)) := by
  rw [nsMap]


-- ============================================================
-- nsSub_compute (NamespaceProps.lean)
-- The rewrite inserts a size guard on the recursive call; we show the guard
-- is always satisfied on the values `alistSub` inspects.
-- ============================================================

theorem ALOOKUP_some_mem' {α β : Type} [BEq α] {l : List (α × β)} {k : α} {b : β}
    (h : ALOOKUP l k = some b) : ∃ k', (k', b) ∈ l := by
  induction l with
  | nil => simp [ALOOKUP] at h
  | cons p l ih =>
    obtain ⟨a, c⟩ := p
    simp only [ALOOKUP] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨a, List.mem_cons_self ..⟩
    · obtain ⟨k', hk⟩ := ih h; exact ⟨k', List.mem_cons_of_mem _ hk⟩

theorem alist_rel_restr_congr {k v1 v2 : Type} [BEq k] (R R' : k → v1 → v2 → Prop)
    (l1 : List (k × v1)) (l2 : List (k × v2)) (keys : List k)
    (hR : ∀ kk a b, (∃ k', (k', a) ∈ l1) → (R kk a b ↔ R' kk a b)) :
    alist_rel_restr R l1 l2 keys ↔ alist_rel_restr R' l1 l2 keys := by
  induction keys with
  | nil => simp [alist_rel_restr]
  | cons k1 keys ih =>
    simp only [alist_rel_restr]
    rcases h1 : ALOOKUP l1 k1 with _ | val1
    · exact Iff.rfl
    · rcases h2 : ALOOKUP l2 k1 with _ | val2
      · exact Iff.rfl
      · dsimp only
        rw [hR _ _ _ (ALOOKUP_some_mem' h1), ih]

theorem nsSub_compute_orig_eqn {m n v1 v2 : Type} [BEq m] [BEq n]
    (path : List m) (R : cml_id m n → v1 → v2 → Prop)
    (e1V : List (n × v1)) (e1M : List (m × «namespace» m n v1))
    (e2V : List (n × v2)) (e2M : List (m × «namespace» m n v2)) :
    nsSub_compute path R (.Bind e1V e1M) (.Bind e2V e2M) =
      (alistSub (fun k val1 val2 => R (mk_id path.reverse k) val1 val2) e1V e2V ∧
       alistSub (fun k val1 val2 => nsSub_compute (k :: path) R val1 val2) e1M e2M) := by
  rw [nsSub_compute]
  apply propext
  apply and_congr Iff.rfl
  unfold alistSub
  apply alist_rel_restr_congr
  intro kk a b ⟨k', hmem⟩
  have hs : sizeOf a < sizeOf («namespace».Bind e1V e1M) := by
    have := List.sizeOf_lt_of_mem hmem
    simp_all
    omega
  simp only [if_pos hs]

-- ============================================================
-- Evaluator (Evaluate.lean): evaluate, evaluate_match, evaluate_decs
-- ============================================================

macro "eqn_tac" : tactic => `(tactic| (
  (try simp only [dite_eq_ite])
  repeat' (first | rfl | (split <;> (rename_i heq; simp only [heq])))))

theorem evaluate_orig_eqn {ffi : Type} (st : cml_state ffi) (env : sem_env) (es : List exp) :
    evaluate st env es =
  match es with
  | [] => (st, .Rval [])
  | [.Lit l] => (st, .Rval [.Litv l])
  | [.Raise e] =>
    match evaluate st env [e] with
    | (st', .Rval vs) => (st', .Rerr (.Rraise vs.head!))
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Handle e pes] =>
    match fix_clock st (evaluate st env [e]) with
    | (st', .Rval v') => (st', .Rval v')
    | (st', .Rerr (.Rraise val_)) =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) val_ then
        evaluate_match st' env val_ pes val_
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr (.Rabort a)) => (st', .Rerr (.Rabort a))
  | [.Con cn es'] =>
    if do_con_check env.c cn es'.length then
      match evaluate st env es'.reverse with
      | (st', .Rval vs) =>
        match build_conv env.c cn vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some v' => (st', .Rval [v'])
      | (st', .Rerr e) => (st', .Rerr e)
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Var n] =>
    match nsLookup env.v_ n with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some v' => (st, .Rval [v'])
  | [.Fun x e] => (st, .Rval [.Closure env x e])
  | [.App o_ es'] =>
    match fix_clock st (evaluate st env es'.reverse) with
    | (st', .Rval vs) =>
      match getOpClass o_ with
      | .FunApp =>
        match do_opapp vs.reverse with
        | some (env', e) =>
          if st'.clock == 0 then (st', .Rerr (.Rabort .Rtimeout_error))
          else evaluate (dec_clock st') env' [e]
        | none => (st', .Rerr (.Rabort .Rtype_error))
      | .Force =>
        match dest_thunk vs.reverse st'.refs with
        | .BadRef => (st', .Rerr (.Rabort .Rtype_error))
        | .NotThunk => (st', .Rerr (.Rabort .Rtype_error))
        | .IsThunk .Evaluated val_ => (st', .Rval [val_])
        | .IsThunk .NotEvaluated f =>
          match do_opapp [f, .Conv none []] with
          | some (env', e) =>
            if st'.clock == 0 then (st', .Rerr (.Rabort .Rtimeout_error))
            else
              match evaluate (dec_clock st') env' [e] with
              | (st2, .Rval vs2) =>
                match update_thunk vs.reverse st2.refs vs2 with
                | none => (st2, .Rerr (.Rabort .Rtype_error))
                | some refs => ({ st2 with refs := refs }, .Rval vs2)
              | (st2, .Rerr e) => (st2, .Rerr e)
          | none => (st', .Rerr (.Rabort .Rtype_error))
      | .EvalOp =>
        match fix_clock st' (do_eval_res vs.reverse st') with
        | (st1, .Rval (env1, decs)) =>
          if st1.clock == 0 then (st1, .Rerr (.Rabort .Rtimeout_error))
          else
            match fix_clock (dec_clock st1)
                    (evaluate_decs (dec_clock st1) env1 decs) with
            | (st2, .Rval env2) =>
              match declare_env st2.eval_state_field (extend_dec_env env2 env1) with
              | some (x, es2) =>
                ({ st2 with eval_state_field :=
                    reset_env_generation st'.eval_state_field es2 }, .Rval [x])
              | none => (st2, .Rerr (.Rabort .Rtype_error))
            | (st2, .Rerr (.Rabort a)) => (st2, .Rerr (.Rabort a))
            | (st2, .Rerr e) =>
              ({ st2 with eval_state_field :=
                  reset_env_generation st'.eval_state_field st2.eval_state_field },
               .Rerr e)
        | (st1, .Rerr e) => (st1, .Rerr e)
      | .Simple =>
        match do_app (st'.refs, st'.ffi) o_ vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some ((refs, ffi_), r) =>
          ({ st' with refs := refs, ffi := ffi_ }, list_result r)
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Log l e1 e2] =>
    match fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match do_log l v1.head! e2 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some (.Exp e) => evaluate st' env [e]
      | some (.Val v') => (st', .Rval [v'])
    | (st', .Rerr e) => (st', .Rerr e)
  | [.If e1 e2 e3] =>
    match fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v') =>
      match do_if v'.head! e2 e3 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some e => evaluate st' env [e]
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Mat e pes] =>
    match fix_clock st (evaluate st env [e]) with
    | (st', .Rval v') =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v'.head! then
        evaluate_match st' env v'.head! pes bind_exn_v
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Let xo e1 e2] =>
    match fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v') =>
      evaluate st' (.mk (nsOptBind xo v'.head! env.v_) env.c) [e2]
    | (st', .Rerr e) => (st', .Rerr e)
  | [.Letrec funs e] =>
    if ALL_DISTINCT (funs.map fun (x, _, _) => x) then
      evaluate st (.mk (build_rec_env funs env env.v_) env.c) [e]
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Tannot e _] => evaluate st env [e]
  | [.Lannot e _] => evaluate st env [e]
  | e1 :: e2 :: es' =>
    match fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match evaluate st' env (e2 :: es') with
      | (st'', .Rval vs) => (st'', .Rval (v1.head! :: vs))
      | (st'', .Rerr e) => (st'', .Rerr e)
    | (st', .Rerr e) => (st', .Rerr e) := by
  conv => lhs; rw [evaluate.eq_def]
  rcases es with _ | ⟨e, _ | ⟨e2, es'⟩⟩
  · rfl
  · cases e <;> (try dsimp only) <;> eqn_tac
  · (try dsimp only); eqn_tac

theorem evaluate_match_orig_eqn {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (val_ : v) (pes : List (pat × exp)) (err_v : v) :
    evaluate_match st env val_ pes err_v =
  match pes with
  | [] => (st, .Rerr (.Rraise err_v))
  | (p, e) :: pes' =>
    if ALL_DISTINCT (pat_bindings p []) then
      match pmatch env.c st.refs p val_ [] with
      | .No_match => evaluate_match st env val_ pes' err_v
      | .Match_type_error => (st, .Rerr (.Rabort .Rtype_error))
      | .Match env_v' =>
        evaluate st (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e]
    else (st, .Rerr (.Rabort .Rtype_error)) := by
  conv => lhs; rw [evaluate_match.eq_def]
  rcases pes with _ | ⟨⟨p, e⟩, pes'⟩
  · rfl
  · (try dsimp only); eqn_tac

theorem evaluate_decs_orig_eqn {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (ds : List dec) :
    evaluate_decs st env ds =
  match ds with
  | [] => (st, .Rval (.mk nsEmpty nsEmpty))
  | [.Dlet _ p e] =>
    if ALL_DISTINCT (pat_bindings p []) && every_exp (one_con_check env.c) e then
      match evaluate st env [e] with
      | (st', .Rval v') =>
        (st', match pmatch env.c st'.refs p v'.head! [] with
          | .No_match => .Rerr (.Rraise bind_exn_v)
          | .Match_type_error => .Rerr (.Rabort .Rtype_error)
          | .Match new_vals => .Rval (.mk (alist_to_ns new_vals) nsEmpty))
      | (st', .Rerr err) => (st', .Rerr err)
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Dletrec _ funs] =>
    (st,
     if ALL_DISTINCT (funs.map fun (x, _, _) => x) &&
        funs.all fun (_, _, e) => every_exp (one_con_check env.c) e then
       .Rval (.mk (build_rec_env funs env nsEmpty) nsEmpty)
     else .Rerr (.Rabort .Rtype_error))
  | [.Dtype _ tds] =>
    if tds.all check_dup_ctors then
      ({ st with next_type_stamp := st.next_type_stamp + tds.length },
       .Rval (.mk nsEmpty (build_tdefs st.next_type_stamp tds)))
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Dtabbrev _ _ _ _] =>
    (st, .Rval (.mk nsEmpty nsEmpty))
  | [.Denv n] =>
    match declare_env st.eval_state_field env with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some (x, es') =>
      ({ st with eval_state_field := es' }, .Rval (.mk (nsSing n x) nsEmpty))
  | [.Dexn _ cn ts] =>
    ({ st with next_exn_stamp := st.next_exn_stamp + 1 },
     .Rval (.mk nsEmpty (nsSing cn (ts.length, .ExnStamp st.next_exn_stamp))))
  | [.Dmod mn ds'] =>
    match evaluate_decs st env ds' with
    | (st', r) =>
      (st', match r with
        | .Rval env' => .Rval (.mk (nsLift mn env'.v_) (nsLift mn env'.c))
        | .Rerr err => .Rerr err)
  | [.Dlocal lds ds'] =>
    match fix_clock st (evaluate_decs st env lds) with
    | (st1, .Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds'
    | (st1, .Rerr e) => (st1, .Rerr e)
  | d1 :: d2 :: ds' =>
    match fix_clock st (evaluate_decs st env [d1]) with
    | (st1, .Rval env1) =>
      match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds') with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, .Rerr e) => (st1, .Rerr e) := by
  conv => lhs; rw [evaluate_decs.eq_def]
  rcases ds with _ | ⟨d, _ | ⟨d2, ds'⟩⟩
  · rfl
  · cases d <;> (try dsimp only) <;> eqn_tac
  · (try dsimp only); eqn_tac

-- ============================================================
-- CARD (HOL4Prelude.lean): agrees with HOL4 CARD on finite sets
-- (any duplicate-free enumeration determines the value).
-- ============================================================

theorem CARD_nodup_spec {α : Type} (s : Set α) (l : List α) (hl : l.Nodup)
    (hs : ∀ a, s a ↔ a ∈ l) : CARD s = l.length :=
  CARD_eq_of_nodup hl hs

#print axioms every_exp_orig_eqn
#print axioms check_freevars_orig_eqn
#print axioms check_freevars_ast_orig_eqn
#print axioms check_type_names_orig_eqn
#print axioms is_value_orig_eqn
#print axioms pmatch_orig_eqn
#print axioms pmatch_list_orig_eqn
#print axioms do_eq_orig_eqn
#print axioms do_eq_list_orig_eqn
#print axioms concrete_v_orig_eqn
#print axioms concrete_v_list_orig_eqn
#print axioms nsMap_orig_eqn
#print axioms nsSub_compute_orig_eqn
#print axioms evaluate_orig_eqn
#print axioms evaluate_match_orig_eqn
#print axioms evaluate_decs_orig_eqn
#print axioms CARD_nodup_spec
