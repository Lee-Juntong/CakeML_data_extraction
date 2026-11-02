import LeanTypeSound

/-!
# Round-1 termination rewrites agree with the original definitions

Endpoint: Docs round 1 (commit 0d1173557). Originals: frozen baseline commit 252eab2cf.

Six definitions were rewritten with `List.attach` to prove termination:
every_exp, check_freevars, check_freevars_ast, check_type_names, is_value, nsMap.

Part 1: each rewritten definition satisfies the original defining equation
(`f args = original body`, recursive calls to the new `f`). No sorry.

Part 2: the original definitions, copied verbatim from 252eab2cf into namespace
`Old` with their admitted termination (`decreasing_by all_goals sorry` /
`decreasing_by sorry`).

Part 3: `Old.f args = f args`, by well-founded recursion on `sizeOf`.
These depend on `sorryAx` only through the copied `Old` definitions.
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
-- nsMap (Namespace.lean)
-- ============================================================

theorem nsMap_orig_eqn {m n v w : Type} (f : v → w) (vals : List (n × v))
    (mods : List (m × «namespace» m n v)) :
    nsMap f (.Bind vals mods) =
      .Bind (vals.map fun (name, x) => (name, f x))
            (mods.map fun (mn, e) => (mn, nsMap f e)) := by
  rw [nsMap]
  congr 1
  conv => rhs; rw [← List.attach_map_subtype_val mods, List.map_map]
  rfl


-- ============================================================
-- Original definitions (commit 252eab2cf), verbatim, in namespace Old
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

-- Namespace.lean
def nsMap {m n v w : Type} (f : v → w) : «namespace» m n v → «namespace» m n w
  | .Bind vals mods =>
    .Bind (vals.map fun (name, x) => (name, f x))
          (mods.map fun (mn, e) => (mn, nsMap f e))
  decreasing_by sorry

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

#print axioms every_exp_orig_eqn
#print axioms check_freevars_orig_eqn
#print axioms check_freevars_ast_orig_eqn
#print axioms check_type_names_orig_eqn
#print axioms is_value_orig_eqn
#print axioms nsMap_orig_eqn
#print axioms every_exp_old_eq_new
#print axioms check_freevars_old_eq_new
#print axioms check_freevars_ast_old_eq_new
#print axioms check_type_names_old_eq_new
#print axioms is_value_old_eq_new
#print axioms nsMap_old_eq_new
