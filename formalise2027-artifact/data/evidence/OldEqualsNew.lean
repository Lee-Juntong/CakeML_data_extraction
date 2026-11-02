import LeanTypeSound

/-!
# The original (admitted-termination) definitions equal the rewritten ones

Part 1 repeats `OrigEquations.lean`: each rewritten (terminating) definition
satisfies the defining equation of the original definition.

Part 2 copies the original definitions verbatim from commit de795c9f6 into
namespace `Old`, including their admitted termination clauses
(`decreasing_by all_goals sorry`, `termination_by 0`). Inside `Old`, recursive
calls and calls to other copied definitions (for example `pmatch` in
`Old.evaluate_match`, `every_exp` in `Old.evaluate_decs`) refer to the `Old`
versions; everything else refers to the project constants.

Part 3 proves `Old.f args = f args` for each definition, by well-founded
induction on the measure of the rewritten definition. These theorems depend on
`sorryAx` only through the admitted termination of the `Old` definitions.
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

-- ============================================================
-- Original definitions (commit de795c9f6), verbatim, in namespace Old
-- ============================================================

namespace Old

-- Ast.lean
def every_exp (p : exp → Bool) : exp → Bool
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
    p (.Letrec funs e) && every_exp p e && funs.all fun (_, _, e') => every_exp p e'
  decreasing_by all_goals sorry

-- TypeSystem.lean
def check_freevars : Nat → List mlstring → sem_t → Bool
  | _, tvs, .Tvar tv => tvs.any (· == tv)
  | dbmax, tvs, .Tapp ts _ => ts.all (check_freevars dbmax tvs)
  | dbmax, _, .Tvar_db n => n < dbmax
decreasing_by all_goals sorry

def check_freevars_ast : List mlstring → ast_t → Bool
  | tvs, .Atvar tv => tvs.any (· == tv)
  | tvs, .Attup ts => ts.all (check_freevars_ast tvs)
  | tvs, .Atfun t1 t2 => check_freevars_ast tvs t1 && check_freevars_ast tvs t2
  | tvs, .Atapp ts _ => ts.all (check_freevars_ast tvs)
decreasing_by all_goals sorry

def check_type_names (tenvT : tenv_abbrev) : ast_t → Bool
  | .Atvar _ => true
  | .Attup ts => ts.all (check_type_names tenvT)
  | .Atfun t1 t2 => check_type_names tenvT t1 && check_type_names tenvT t2
  | .Atapp ts tn =>
    (match nsLookup tenvT tn with
     | some (tvs, _) => tvs.length == ts.length
     | none => false) &&
    ts.all (check_type_names tenvT)
decreasing_by all_goals sorry

def is_value : exp → Bool
  | .Lit _ => true
  | .Con _ es => es.all is_value
  | .Var _ => true
  | .Fun _ _ => true
  | .Tannot e _ => is_value e
  | .Lannot e _ => is_value e
  | _ => false
decreasing_by all_goals sorry

-- SemanticPrimitives.lean
mutual
def pmatch (envC : env_ctor) (s : store v) : pat → v → alist varN v →
    match_result (alist varN v)
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
  | _, _, _ => .Match_type_error
  termination_by 0
  decreasing_by all_goals sorry

def pmatch_list (envC : env_ctor) (s : store v) :
    List pat → List v → alist varN v → match_result (alist varN v)
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
  | _, _, _ => .Match_type_error
  termination_by 0
  decreasing_by all_goals sorry
end

mutual
def do_eq : v → v → eq_result
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
  | _, _ => .Eq_type_error
  termination_by 0
  decreasing_by all_goals sorry

def do_eq_list : List v → List v → eq_result
  | [], [] => .Eq_val true
  | v1 :: vs1, v2 :: vs2 =>
    match do_eq v1 v2 with
    | .Eq_val r => if !r then .Eq_val false else do_eq_list vs1 vs2
    | .Eq_type_error => .Eq_type_error
  | _, _ => .Eq_val false
  termination_by 0
  decreasing_by all_goals sorry
end

mutual
def concrete_v : v → Bool
  | .Loc _ _ => true
  | .Litv _ => true
  | .Conv _ vs => concrete_v_list vs
  | .Vectorv vs => concrete_v_list vs
  | _ => false
  termination_by 0
  decreasing_by all_goals sorry

def concrete_v_list : List v → Bool
  | [] => true
  | val_ :: vs => concrete_v val_ && concrete_v_list vs
  termination_by 0
  decreasing_by all_goals sorry
end

-- Namespace.lean
def nsMap {m n v w : Type} (f : v → w) : «namespace» m n v → «namespace» m n w
  | .Bind vals mods =>
    .Bind (vals.map fun (name, x) => (name, f x))
          (mods.map fun (mn, e) => (mn, nsMap f e))
  decreasing_by sorry

-- NamespaceProps.lean
def nsSub_compute {m n v1 v2 : Type} [BEq m] [BEq n]
    (path : List m) (R : cml_id m n → v1 → v2 → Prop) :
    «namespace» m n v1 → «namespace» m n v2 → Prop
  | .Bind e1V e1M, .Bind e2V e2M =>
    alistSub (fun k val1 val2 => R (mk_id path.reverse k) val1 val2) e1V e2V ∧
    alistSub (fun k val1 val2 => nsSub_compute (k :: path) R val1 val2) e1M e2M
  decreasing_by all_goals sorry

-- Evaluate.lean
mutual
def evaluate {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (es : List exp) : cml_state ffi × result (List v) v :=
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
    | (st', .Rerr e) => (st', .Rerr e)
  termination_by 0
  decreasing_by all_goals sorry

def evaluate_match {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (val_ : v) (pes : List (pat × exp)) (err_v : v) :
    cml_state ffi × result (List v) v :=
  match pes with
  | [] => (st, .Rerr (.Rraise err_v))
  | (p, e) :: pes' =>
    if ALL_DISTINCT (pat_bindings p []) then
      match pmatch env.c st.refs p val_ [] with
      | .No_match => evaluate_match st env val_ pes' err_v
      | .Match_type_error => (st, .Rerr (.Rabort .Rtype_error))
      | .Match env_v' =>
        evaluate st (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e]
    else (st, .Rerr (.Rabort .Rtype_error))
  termination_by 0
  decreasing_by all_goals sorry

def evaluate_decs {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (ds : List dec) : cml_state ffi × result sem_env v :=
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
    | (st1, .Rerr e) => (st1, .Rerr e)
  termination_by 0
  decreasing_by all_goals sorry
end

end Old

-- ============================================================
-- Old = New
-- ============================================================

theorem all_congr_mem {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem every_exp_old_eq_new (p : exp → Bool) (e : exp) :
    Old.every_exp p e = every_exp p e := by
  rw [Old.every_exp.eq_def, every_exp_orig_eqn]
  cases e with
  | Raise e => dsimp only; simp only [every_exp_old_eq_new p e]
  | Handle e pes =>
    dsimp only
    simp only [every_exp_old_eq_new p e]
    congr 1
    exact all_congr_mem fun x hx => by
      obtain ⟨a, b⟩ := x
      have := List.sizeOf_lt_of_mem hx
      exact every_exp_old_eq_new p b
  | Lit l => rfl
  | Con cn es =>
    dsimp only
    congr 1
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact every_exp_old_eq_new p x
  | Var v => rfl
  | Fun x e => dsimp only; simp only [every_exp_old_eq_new p e]
  | App o es =>
    dsimp only
    congr 1
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact every_exp_old_eq_new p x
  | Log l e1 e2 => dsimp only; simp only [every_exp_old_eq_new p e1, every_exp_old_eq_new p e2]
  | If e1 e2 e3 =>
    dsimp only
    simp only [every_exp_old_eq_new p e1, every_exp_old_eq_new p e2, every_exp_old_eq_new p e3]
  | Mat e pes =>
    dsimp only
    simp only [every_exp_old_eq_new p e]
    congr 1
    exact all_congr_mem fun x hx => by
      obtain ⟨a, b⟩ := x
      have := List.sizeOf_lt_of_mem hx
      exact every_exp_old_eq_new p b
  | Let x e1 e2 => dsimp only; simp only [every_exp_old_eq_new p e1, every_exp_old_eq_new p e2]
  | Tannot e a => dsimp only; simp only [every_exp_old_eq_new p e]
  | Lannot e a => dsimp only; simp only [every_exp_old_eq_new p e]
  | Letrec funs e =>
    dsimp only
    simp only [every_exp_old_eq_new p e]
    congr 1
    exact all_congr_mem fun x hx => by
      obtain ⟨a, b, c⟩ := x
      have := List.sizeOf_lt_of_mem hx
      exact every_exp_old_eq_new p c
termination_by sizeOf e
decreasing_by all_goals (simp_all; try omega)

theorem check_freevars_old_eq_new (n : Nat) (ls : List mlstring) (t : sem_t) :
    Old.check_freevars n ls t = check_freevars n ls t := by
  rw [Old.check_freevars.eq_def, check_freevars_orig_eqn]
  cases t with
  | Tvar tv => rfl
  | Tapp ts tn =>
    dsimp only
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact check_freevars_old_eq_new n ls x
  | Tvar_db k => rfl
termination_by sizeOf t
decreasing_by all_goals (simp_all; try omega)

theorem check_freevars_ast_old_eq_new (ls : List mlstring) (t : ast_t) :
    Old.check_freevars_ast ls t = check_freevars_ast ls t := by
  rw [Old.check_freevars_ast.eq_def, check_freevars_ast_orig_eqn]
  cases t with
  | Atvar tv => rfl
  | Attup ts =>
    dsimp only
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact check_freevars_ast_old_eq_new ls x
  | Atfun t1 t2 =>
    dsimp only
    simp only [check_freevars_ast_old_eq_new ls t1, check_freevars_ast_old_eq_new ls t2]
  | Atapp ts tn =>
    dsimp only
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact check_freevars_ast_old_eq_new ls x
termination_by sizeOf t
decreasing_by all_goals (simp_all; try omega)

theorem check_type_names_old_eq_new (tenvT : tenv_abbrev) (t : ast_t) :
    Old.check_type_names tenvT t = check_type_names tenvT t := by
  rw [Old.check_type_names.eq_def, check_type_names_orig_eqn]
  cases t with
  | Atvar tv => rfl
  | Attup ts =>
    dsimp only
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact check_type_names_old_eq_new tenvT x
  | Atfun t1 t2 =>
    dsimp only
    simp only [check_type_names_old_eq_new tenvT t1, check_type_names_old_eq_new tenvT t2]
  | Atapp ts tn =>
    dsimp only
    congr 1
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact check_type_names_old_eq_new tenvT x
termination_by sizeOf t
decreasing_by all_goals (simp_all; try omega)

theorem is_value_old_eq_new (e : exp) : Old.is_value e = is_value e := by
  rw [Old.is_value.eq_def, is_value_orig_eqn]
  cases e with
  | Con cn es =>
    dsimp only
    exact all_congr_mem fun x hx => by
      have := List.sizeOf_lt_of_mem hx
      exact is_value_old_eq_new x
  | Tannot e a => dsimp only; exact is_value_old_eq_new e
  | Lannot e a => dsimp only; exact is_value_old_eq_new e
  | _ => rfl
termination_by sizeOf e
decreasing_by all_goals (simp_all; try omega)

mutual
theorem pmatch_old_eq_new (envC : env_ctor) (s : store v) : ∀ (p : pat) (w : v)
    (env : alist varN v), Old.pmatch envC s p w env = pmatch envC s p w env
  | .Pcon o ps, w, env => by
    have ih := pmatch_list_old_eq_new envC s ps
    rw [Old.pmatch.eq_def, pmatch_orig_eqn]
    rcases o with _ | _ <;>
    rcases w with _ | ⟨_ | _, vs⟩ | _ | _ | _ | _ | _ <;> (try dsimp only) <;>
    (try simp only [ih])
  | .Pref p, w, env => by
    have ih := pmatch_old_eq_new envC s p
    rw [Old.pmatch.eq_def, pmatch_orig_eqn]
    rcases w with _ | ⟨_ | _, vs⟩ | _ | _ | _ | _ | _ <;> (try dsimp only) <;>
    (try simp only [ih])
  | .Pas p i, w, env => by
    have ih := pmatch_old_eq_new envC s p
    rw [Old.pmatch.eq_def, pmatch_orig_eqn]
    exact ih _ _
  | .Ptannot p t, w, env => by
    have ih := pmatch_old_eq_new envC s p
    rw [Old.pmatch.eq_def, pmatch_orig_eqn]
    exact ih _ _
  | .Pany, w, env => by rw [Old.pmatch.eq_def, pmatch_orig_eqn]
  | .Pvar x, w, env => by rw [Old.pmatch.eq_def, pmatch_orig_eqn]
  | .Plit l, w, env => by
    rw [Old.pmatch.eq_def, pmatch_orig_eqn]
    rcases w with _ | ⟨_ | _, vs⟩ | _ | _ | _ | _ | _ <;> rfl
termination_by p => sizeOf p

theorem pmatch_list_old_eq_new (envC : env_ctor) (s : store v) : ∀ (ps : List pat)
    (vs : List v) (env : alist varN v),
    Old.pmatch_list envC s ps vs env = pmatch_list envC s ps vs env
  | [], vs, env => by
    rw [Old.pmatch_list.eq_def, pmatch_list_orig_eqn]
    rcases vs with _ | _ <;> rfl
  | p :: ps, vs, env => by
    have ih1 := pmatch_old_eq_new envC s p
    have ih2 := pmatch_list_old_eq_new envC s ps
    rw [Old.pmatch_list.eq_def, pmatch_list_orig_eqn]
    rcases vs with _ | _ <;> (try dsimp only) <;> (try simp only [ih1, ih2])
termination_by ps => sizeOf ps
end

mutual
theorem do_eq_old_eq_new : ∀ (a b : v), Old.do_eq a b = do_eq a b
  | .Conv cn vs1, b => by
    have ih := do_eq_list_old_eq_new vs1
    rw [Old.do_eq.eq_def, do_eq_orig_eqn]
    rcases b with _ | ⟨_, vs2⟩ | _ | _ | _ | vs2 | ⟨_, ⟨_, _⟩⟩ <;> (try dsimp only) <;>
    (try simp only [ih])
  | .Vectorv vs1, b => by
    have ih := do_eq_list_old_eq_new vs1
    rw [Old.do_eq.eq_def, do_eq_orig_eqn]
    rcases b with _ | ⟨_, vs2⟩ | _ | _ | _ | vs2 | ⟨_, ⟨_, _⟩⟩ <;> (try dsimp only) <;>
    (try simp only [ih])
  | .Litv _, b | .Closure _ _ _, b | .Recclosure _ _ _, b | .Loc _ _, b | .Env _ ⟨_, _⟩, b => by
    rw [Old.do_eq.eq_def, do_eq_orig_eqn]
    rcases b with _ | ⟨_, vs2⟩ | _ | _ | _ | vs2 | ⟨_, ⟨_, _⟩⟩ <;> rfl
termination_by a => sizeOf a

theorem do_eq_list_old_eq_new : ∀ (a b : List v), Old.do_eq_list a b = do_eq_list a b
  | [], b => by
    rw [Old.do_eq_list.eq_def, do_eq_list_orig_eqn]
    rcases b with _ | _ <;> rfl
  | x :: a, b => by
    have ih1 := do_eq_old_eq_new x
    have ih2 := do_eq_list_old_eq_new a
    rw [Old.do_eq_list.eq_def, do_eq_list_orig_eqn]
    rcases b with _ | _ <;> (try dsimp only) <;> (try simp only [ih1, ih2])
termination_by a => sizeOf a
end

mutual
theorem concrete_v_old_eq_new : ∀ (a : v), Old.concrete_v a = concrete_v a
  | .Conv _ vs => by
    have ih := concrete_v_list_old_eq_new vs
    rw [Old.concrete_v.eq_def, concrete_v_orig_eqn]
    exact ih
  | .Vectorv vs => by
    have ih := concrete_v_list_old_eq_new vs
    rw [Old.concrete_v.eq_def, concrete_v_orig_eqn]
    exact ih
  | .Litv _ | .Closure _ _ _ | .Recclosure _ _ _ | .Loc _ _ | .Env _ _ => by
    rw [Old.concrete_v.eq_def, concrete_v_orig_eqn]
termination_by a => sizeOf a

theorem concrete_v_list_old_eq_new : ∀ (a : List v), Old.concrete_v_list a = concrete_v_list a
  | [] => by rw [Old.concrete_v_list.eq_def, concrete_v_list_orig_eqn]
  | x :: a => by
    have ih1 := concrete_v_old_eq_new x
    have ih2 := concrete_v_list_old_eq_new a
    rw [Old.concrete_v_list.eq_def, concrete_v_list_orig_eqn]
    dsimp only
    rw [ih1, ih2]
termination_by a => sizeOf a
end

theorem nsMap_old_eq_new {m n v w : Type} (f : v → w) (ns : «namespace» m n v) :
    Old.nsMap f ns = nsMap f ns := by
  rcases ns with ⟨vals, mods⟩
  rw [Old.nsMap.eq_def, nsMap_orig_eqn]
  dsimp only
  congr 1
  apply List.map_congr_left
  intro ⟨mn, e⟩ hx
  have := List.sizeOf_lt_of_mem hx
  dsimp only
  rw [nsMap_old_eq_new f e]
termination_by sizeOf ns
decreasing_by all_goals (simp_all; try omega)

theorem nsSub_compute_old_eq_new {m n v1 v2 : Type} [BEq m] [BEq n]
    (path : List m) (R : cml_id m n → v1 → v2 → Prop)
    (a : «namespace» m n v1) (b : «namespace» m n v2) :
    Old.nsSub_compute path R a b = nsSub_compute path R a b := by
  rcases a with ⟨e1V, e1M⟩
  rcases b with ⟨e2V, e2M⟩
  rw [Old.nsSub_compute.eq_def, nsSub_compute_orig_eqn]
  dsimp only
  apply propext
  apply and_congr Iff.rfl
  unfold alistSub
  apply alist_rel_restr_congr
  intro kk x y ⟨k', hmem⟩
  have := List.sizeOf_lt_of_mem hmem
  rw [nsSub_compute_old_eq_new (kk :: path) R x y]
termination_by sizeOf a
decreasing_by all_goals (simp_all; try omega)

theorem Old.evaluate_cons_cons {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (e1 e2 : exp) (es' : List exp) :
    Old.evaluate st env (e1 :: e2 :: es') =
    match fix_clock st (Old.evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match Old.evaluate st' env (e2 :: es') with
      | (st'', .Rval vs) => (st'', .Rval (v1.head! :: vs))
      | (st'', .Rerr e) => (st'', .Rerr e)
    | (st', .Rerr e) => (st', .Rerr e) := by
  rw [Old.evaluate.eq_def]; cases e1 <;> rfl

theorem evaluate_cons_cons {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (e1 e2 : exp) (es' : List exp) :
    evaluate st env (e1 :: e2 :: es') =
    match fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match evaluate st' env (e2 :: es') with
      | (st'', .Rval vs) => (st'', .Rval (v1.head! :: vs))
      | (st'', .Rerr e) => (st'', .Rerr e)
    | (st', .Rerr e) => (st', .Rerr e) := by
  rw [evaluate_orig_eqn]; cases e1 <;> rfl

theorem Old.evaluate_decs_cons_cons {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (d1 d2 : dec) (ds' : List dec) :
    Old.evaluate_decs st env (d1 :: d2 :: ds') =
    match fix_clock st (Old.evaluate_decs st env [d1]) with
    | (st1, .Rval env1) =>
      match Old.evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds') with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, .Rerr e) => (st1, .Rerr e) := by
  rw [Old.evaluate_decs.eq_def]; cases d1 <;> rfl

theorem evaluate_decs_cons_cons {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (d1 d2 : dec) (ds' : List dec) :
    evaluate_decs st env (d1 :: d2 :: ds') =
    match fix_clock st (evaluate_decs st env [d1]) with
    | (st1, .Rval env1) =>
      match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds') with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, .Rerr e) => (st1, .Rerr e) := by
  rw [evaluate_decs_orig_eqn]; cases d1 <;> rfl

-- ============================================================
-- Evaluator: well-founded induction on the new measure (st.clock, sizeOf _)
-- ============================================================

set_option hygiene false in
macro "old_new_dec" : tactic => `(tactic| (
  all_goals first
    | (apply lex_le_lt (Nat.le_refl _); (try simp only [list_sizeOf_reverse]); simp <;> omega)
    | (apply lex_le_lt (Nat.le_refl _); have := pat_sizeOf_pos ‹_›; simp <;> omega)
    | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List exp›; simp <;> omega)
    | (apply lex_le_lt (Nat.le_refl _); have := list_sizeOf_pos ‹List dec›; simp <;> omega)
    | (apply lex_le_lt (fix_clock_clock_le _hfc); simp <;> omega)
    | (apply lex_le_lt (fix_clock_clock_le _hfc); have := pat_sizeOf_pos ‹_›; simp <;> omega)
    | (apply lex_lt; have := fix_clock_clock_le _hfc; have := fix_clock_clock_le _hfc1;
       simp [dec_clock] at *; omega)
    | (apply lex_lt; have := fix_clock_clock_le _hfc; simp [dec_clock] at *; omega)
    | (apply lex_le_lt (fix_clock_clock_le _hfc); rw [do_log_exp _hlog]; simp <;> omega)
    | (apply lex_le_lt (fix_clock_clock_le _hfc)
       rcases do_if_exp _hif with h | h <;> rw [h] <;> simp <;> omega)))

mutual
theorem evaluate_old_eq_new {ffi : Type} (st : cml_state ffi) (env : sem_env) (es : List exp) :
    Old.evaluate st env es = evaluate st env es := by
  rcases es with _ | ⟨e, _ | ⟨e2, es'⟩⟩
  · (rw [Old.evaluate.eq_def, evaluate_orig_eqn]) <;> rfl
  · rw [Old.evaluate.eq_def, evaluate_orig_eqn]
    cases e with
    | Raise e =>
      dsimp only
      rw [evaluate_old_eq_new st env [e]]
    | Handle e pes =>
      dsimp only
      rw [evaluate_old_eq_new st env [e]]
      cases _hfc : fix_clock st (evaluate st env [e]) with
      | mk st' r =>
        rcases r with vs | (val_ | a)
        · rfl
        · dsimp only
          split
          · rw [evaluate_match_old_eq_new st' env val_ pes val_]
          · rfl
        · rfl
    | Con cn es' =>
      dsimp only
      rw [evaluate_old_eq_new st env es'.reverse]
    | App o_ es' =>
      dsimp only
      rw [evaluate_old_eq_new st env es'.reverse]
      cases _hfc : fix_clock st (evaluate st env es'.reverse) with
      | mk st' r =>
        rcases r with vs | err
        · dsimp only
          cases getOpClass o_ with
          | FunApp =>
            dsimp only
            cases do_opapp vs.reverse with
            | none => rfl
            | some p =>
              obtain ⟨env', e⟩ := p
              dsimp only
              split
              · rfl
              · rw [evaluate_old_eq_new (dec_clock st') env' [e]]
          | Simple =>
            rfl
          | Force =>
            dsimp only
            rcases dest_thunk vs.reverse st'.refs with _ | _ | ⟨_ | _, f⟩
            · rfl
            · rfl
            · rfl
            · dsimp only
              cases do_opapp [f, .Conv none []] with
              | none => rfl
              | some p =>
                obtain ⟨env', e⟩ := p
                dsimp only
                split
                · rfl
                · rw [evaluate_old_eq_new (dec_clock st') env' [e]]
          | EvalOp =>
            dsimp only
            cases _hfc1 : fix_clock st' (do_eval_res vs.reverse st') with
            | mk st1 r1 =>
              rcases r1 with ⟨env1, decs⟩ | err1
              · dsimp only
                split
                · rfl
                · rw [evaluate_decs_old_eq_new (dec_clock st1) env1 decs]
              · rfl
        · rfl
    | Log l e1 e2 =>
      dsimp only
      rw [evaluate_old_eq_new st env [e1]]
      cases _hfc : fix_clock st (evaluate st env [e1]) with
      | mk st' r =>
        rcases r with v1 | err
        · dsimp only
          cases _hlog : do_log l v1.head! e2 with
          | none => rfl
          | some x =>
            rcases x with e | v'
            · dsimp only
              rw [evaluate_old_eq_new st' env [e]]
            · rfl
        · rfl
    | If e1 e2 e3 =>
      dsimp only
      rw [evaluate_old_eq_new st env [e1]]
      cases _hfc : fix_clock st (evaluate st env [e1]) with
      | mk st' r =>
        rcases r with v' | err
        · dsimp only
          cases _hif : do_if v'.head! e2 e3 with
          | none => rfl
          | some e =>
            dsimp only
            rw [evaluate_old_eq_new st' env [e]]
        · rfl
    | Mat e pes =>
      dsimp only
      rw [evaluate_old_eq_new st env [e]]
      cases _hfc : fix_clock st (evaluate st env [e]) with
      | mk st' r =>
        rcases r with v' | err
        · dsimp only
          split
          · rw [evaluate_match_old_eq_new st' env v'.head! pes bind_exn_v]
          · rfl
        · rfl
    | Let xo e1 e2 =>
      dsimp only
      rw [evaluate_old_eq_new st env [e1]]
      cases _hfc : fix_clock st (evaluate st env [e1]) with
      | mk st' r =>
        rcases r with v' | err
        · dsimp only
          rw [evaluate_old_eq_new st' (.mk (nsOptBind xo v'.head! env.v_) env.c) [e2]]
        · rfl
    | Letrec funs e =>
      dsimp only
      split
      · rw [evaluate_old_eq_new st (.mk (build_rec_env funs env env.v_) env.c) [e]]
      · rfl
    | Tannot e _ =>
      dsimp only
      rw [evaluate_old_eq_new st env [e]]
    | Lannot e _ =>
      dsimp only
      rw [evaluate_old_eq_new st env [e]]
    | Lit _ => rfl
    | Var _ => rfl
    | Fun _ _ => rfl
  · rw [Old.evaluate_cons_cons, evaluate_cons_cons]
    rw [evaluate_old_eq_new st env [e]]
    cases _hfc : fix_clock st (evaluate st env [e]) with
    | mk st' r =>
      rcases r with v1 | err
      · dsimp only
        rw [evaluate_old_eq_new st' env (e2 :: es')]
      · rfl
termination_by (st.clock, sizeOf es)
decreasing_by old_new_dec

theorem evaluate_match_old_eq_new {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (val_ : v) (pes : List (pat × exp)) (err_v : v) :
    Old.evaluate_match st env val_ pes err_v = evaluate_match st env val_ pes err_v := by
  rw [Old.evaluate_match.eq_def, evaluate_match_orig_eqn]
  rcases pes with _ | ⟨⟨p, e⟩, pes'⟩
  · rfl
  · dsimp only
    rw [pmatch_old_eq_new]
    split
    · cases pmatch env.c st.refs p val_ [] with
      | No_match =>
        dsimp only
        rw [evaluate_match_old_eq_new st env val_ pes' err_v]
      | Match_type_error => rfl
      | Match env_v' =>
        dsimp only
        rw [evaluate_old_eq_new st (.mk (nsAppend (alist_to_ns env_v') env.v_) env.c) [e]]
    · rfl
termination_by (st.clock, sizeOf pes)
decreasing_by old_new_dec

theorem evaluate_decs_old_eq_new {ffi : Type} (st : cml_state ffi) (env : sem_env)
    (ds : List dec) :
    Old.evaluate_decs st env ds = evaluate_decs st env ds := by
  rcases ds with _ | ⟨d, _ | ⟨d2, ds'⟩⟩
  · (rw [Old.evaluate_decs.eq_def, evaluate_decs_orig_eqn]) <;> rfl
  · rw [Old.evaluate_decs.eq_def, evaluate_decs_orig_eqn]
    cases d with
    | Dlet _ p e =>
      dsimp only
      rw [every_exp_old_eq_new]
      split
      · rw [evaluate_old_eq_new st env [e]]
        simp only [pmatch_old_eq_new]
      · rfl
    | Dletrec _ funs =>
      dsimp only
      simp only [every_exp_old_eq_new]
    | Dmod mn ds' =>
      dsimp only
      rw [evaluate_decs_old_eq_new st env ds']
    | Dlocal lds ds' =>
      dsimp only
      rw [evaluate_decs_old_eq_new st env lds]
      cases _hfc : fix_clock st (evaluate_decs st env lds) with
      | mk st1 r =>
        rcases r with env1 | err
        · dsimp only
          rw [evaluate_decs_old_eq_new st1 (extend_dec_env env1 env) ds']
        · rfl
    | _ => rfl
  · rw [Old.evaluate_decs_cons_cons, evaluate_decs_cons_cons]
    rw [evaluate_decs_old_eq_new st env [d]]
    cases _hfc : fix_clock st (evaluate_decs st env [d]) with
    | mk st1 r =>
      rcases r with env1 | err
      · dsimp only
        rw [evaluate_decs_old_eq_new st1 (extend_dec_env env1 env) (d2 :: ds')]
      · rfl
termination_by (st.clock, sizeOf ds)
decreasing_by old_new_dec
end

#print axioms every_exp_old_eq_new
#print axioms check_freevars_old_eq_new
#print axioms check_freevars_ast_old_eq_new
#print axioms check_type_names_old_eq_new
#print axioms is_value_old_eq_new
#print axioms pmatch_old_eq_new
#print axioms pmatch_list_old_eq_new
#print axioms do_eq_old_eq_new
#print axioms do_eq_list_old_eq_new
#print axioms evaluate_old_eq_new
#print axioms evaluate_match_old_eq_new
#print axioms evaluate_decs_old_eq_new
#print axioms nsMap_old_eq_new
#print axioms nsSub_compute_old_eq_new
#print axioms concrete_v_old_eq_new
#print axioms concrete_v_list_old_eq_new
