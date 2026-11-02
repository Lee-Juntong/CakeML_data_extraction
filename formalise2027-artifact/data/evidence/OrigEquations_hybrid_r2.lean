import LeanTypeSound

/-!
# The rewritten (terminating) definitions satisfy the original equations

Each theorem below states that a definition rewritten for termination
satisfies the defining equation(s) of the original definition at commit
4841f993e, with recursive calls referring to the new constant.
Target: the hybrid round-2 endpoint (branch proof2-hybrid).
Target: the second-pass round-2 endpoint (branch proof2-second-pass).
-/

open HOL4

theorem all_attach_comp {α : Type} (l : List α) (g : α → Bool) :
    (l.attach.all fun x => g x.1) = l.all g := by
  simp

theorem map_attach_comp {α β : Type} (l : List α) (g : α → β) :
    (l.attach.map fun x => g x.1) = l.map g := by
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
  congr 1
  exact map_attach_comp mods (fun (y : m × «namespace» m n v) => (y.1, nsMap f y.2))


-- ============================================================
-- v_to_list, v_to_char_list (SemanticPrimitives.lean; bodies unchanged,
-- only the sorry'd termination annotations were replaced)
-- ============================================================

theorem v_to_list_orig_eqn (a : v) :
    v_to_list a =
      match a with
      | .Conv (some stmp) [] =>
        if stmp == .TypeStamp (mlstring.strlit "[]") list_type_num then some [] else none
      | .Conv (some stmp) [v1, v2] =>
        if stmp == .TypeStamp (mlstring.strlit "::") list_type_num then
          match v_to_list v2 with
          | none => none
          | some vs => some (v1 :: vs)
        else none
      | _ => none := by
  rw [v_to_list.eq_def]; rfl

theorem v_to_char_list_orig_eqn (a : v) :
    v_to_char_list a =
      match a with
      | .Conv (some stmp) [] =>
        if stmp == .TypeStamp (mlstring.strlit "[]") list_type_num then some [] else none
      | .Conv (some stmp) [.Litv (.Char c), v'] =>
        if stmp == .TypeStamp (mlstring.strlit "::") list_type_num then
          match v_to_char_list v' with
          | none => none
          | some cs => some (c :: cs)
        else none
      | _ => none := by
  rw [v_to_char_list.eq_def]; rfl

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
#print axioms v_to_list_orig_eqn
#print axioms v_to_char_list_orig_eqn
