/-
  Translation of typeSysPropsScript.sml
  Theorems about the type system.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitivesProps

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition type_pes_def:
  type_pes tvs tvs' tenv tenvE pes t1 t2 ⇔
    (∀(p,e)::set pes.
      ∃bindings.
        ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t1 bindings ∧
        type_e tenv (bind_var_list tvs' bindings tenvE) e t2)
End
-/
def type_pes (tvs tvs' : Nat) (tenv : type_env) (tenvE : tenv_val_exp)
    (pes : List (pat × exp)) (t1 t2 : sem_t) : Prop :=
  ∀ pe, pe ∈ pes →
    ∃ bindings,
      ALL_DISTINCT (pat_bindings pe.1 []) ∧
      type_p tvs tenv pe.1 t1 bindings ∧
      type_e tenv (bind_var_list tvs' bindings tenvE) pe.2 t2

/- HOL4:
Definition deBruijn_subst_tenvE_def:
(deBruijn_subst_tenvE targs Empty = Empty) ∧
(deBruijn_subst_tenvE targs (Bind_tvar tvs env) =
  Bind_tvar tvs (deBruijn_subst_tenvE targs env)) ∧
(deBruijn_subst_tenvE targs (Bind_name x tvs t env) =
  Bind_name x tvs (deBruijn_subst (tvs + num_tvs env)
                                  (MAP (deBruijn_inc 0 (tvs + num_tvs env)) targs)
                                  t)
       (deBruijn_subst_tenvE targs env))
End
-/
def deBruijn_subst_tenvE (targs : List sem_t) : tenv_val_exp → tenv_val_exp
  | .Empty => .Empty
  | .Bind_tvar tvs env => .Bind_tvar tvs (deBruijn_subst_tenvE targs env)
  | .Bind_name x tvs t env =>
    .Bind_name x tvs
      (deBruijn_subst (tvs + num_tvs env)
        (targs.map (deBruijn_inc 0 (tvs + num_tvs env))) t)
      (deBruijn_subst_tenvE targs env)

/- HOL4:
Definition db_merge_def:
(db_merge Empty e = e) ∧
(db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)) ∧
(db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge e1 e2))
End
-/
def db_merge : tenv_val_exp → tenv_val_exp → tenv_val_exp
  | .Empty, e => e
  | .Bind_tvar tvs e1, e2 => .Bind_tvar tvs (db_merge e1 e2)
  | .Bind_name x tvs t e1, e2 => .Bind_name x tvs t (db_merge e1 e2)

/- HOL4:
Definition type_def_to_ctMap_def:
  (type_def_to_ctMap tenvT next_stamp [] [] = []) ∧
  (type_def_to_ctMap tenvT next_stamp ((tvs,tn,ctors)::tds) (id::ids) =
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    REVERSE
      (MAP (\(cn,ts).
        (TypeStamp cn next_stamp, (tvs, MAP (type_name_subst tenvT) ts, id)))
        ctors))
End
-/
def type_def_to_ctMap (tenvT : tenv_abbrev) (next_stamp : Nat) :
    List (List tvarN × mlstring × List (conN × List ast_t)) →
    List type_ident → List (stamp × (List tvarN × List sem_t × type_ident))
  | [], [] => []
  | (tvs, _, ctors) :: tds, id_ :: ids =>
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    (ctors.map fun (cn, ts) =>
      (stamp.TypeStamp cn next_stamp, (tvs, ts.map (type_name_subst tenvT), id_))).reverse
  | _, _ => []

/- HOL4:
Definition tenv_names_def[simp]:
  (tenv_names Empty = {}) ∧
  (tenv_names (Bind_tvar _ e) = tenv_names e) ∧
  (tenv_names (Bind_name n _ _ e) = n INSERT tenv_names e)
End
-/
def tenv_names : tenv_val_exp → Set mlstring
  | .Empty => ∅
  | .Bind_tvar _ e => tenv_names e
  | .Bind_name n _ _ e => {n} ∪ tenv_names e

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem unchanged_tenv[simp] -/
theorem unchanged_tenv : True := by sorry

/- HOL4: Theorem extend_dec_tenv_assoc[simp] -/
theorem extend_dec_tenv_assoc_thm : True := by sorry

/- HOL4: Theorem tenv_val_ok_nsEmpty[simp] -/
theorem tenv_val_ok_nsEmpty : True := by sorry

/- HOL4: Theorem tenv_ctor_ok_nsEmpty[simp] -/
theorem tenv_ctor_ok_nsEmpty : True := by sorry

/- HOL4: Theorem tenv_abbrev_ok_nsEmpty[simp] -/
theorem tenv_abbrev_ok_nsEmpty : True := by sorry

/- HOL4: Theorem tenv_ok_empty[simp] -/
theorem tenv_ok_empty : True := by sorry

/- HOL4: Theorem check_freevars_add -/
theorem check_freevars_add : True := by sorry

/- HOL4: Theorem check_freevars_subst_single -/
theorem check_freevars_subst_single : True := by sorry

/- HOL4: Theorem deBruijn_inc0 -/
theorem deBruijn_inc0 : True := by sorry

/- HOL4: Theorem deBruijn_inc_deBruijn_inc -/
theorem deBruijn_inc_deBruijn_inc : True := by sorry

/- HOL4: Theorem type_subst_deBruijn_inc_list -/
theorem type_subst_deBruijn_inc_list : True := by sorry

/- HOL4: Theorem nil_deBruijn_inc -/
theorem nil_deBruijn_inc : True := by sorry

/- HOL4: Theorem deBruijn_subst_check_freevars -/
theorem deBruijn_subst_check_freevars : True := by sorry

/- HOL4: Theorem deBruijn_subst_check_freevars2 -/
theorem deBruijn_subst_check_freevars2 : True := by sorry

/- HOL4: Theorem check_freevars_subst_inc -/
theorem check_freevars_subst_inc : True := by sorry

/- HOL4: Theorem check_freevars_subst -/
theorem check_freevars_subst : True := by sorry

/- HOL4: Theorem type_subst_deBruijn_subst_list -/
theorem type_subst_deBruijn_subst_list : True := by sorry

/- HOL4: Theorem nil_deBruijn_subst -/
theorem nil_deBruijn_subst : True := by sorry

/- HOL4: Theorem deBruijn_subst2 -/
theorem deBruijn_subst2_thm : True := by sorry

/- HOL4: Theorem type_e_subst_lem3 -/
theorem type_e_subst_lem3 : True := by sorry

/- HOL4: Theorem subst_inc_cancel -/
theorem subst_inc_cancel : True := by sorry

/- HOL4: Theorem deBruijn_subst_id -/
theorem deBruijn_subst_id : True := by sorry

/- HOL4: Theorem deBruijn_subst_freevars -/
theorem deBruijn_subst_freevars : True := by sorry

/- HOL4: Theorem tenv_abbrev_ok_lookup -/
theorem tenv_abbrev_ok_lookup : True := by sorry

/- HOL4: Theorem check_freevars_type_name_subst -/
theorem check_freevars_type_name_subst : True := by sorry

/- HOL4: Theorem tenv_ctor_ok_merge[simp] -/
theorem tenv_ctor_ok_merge : True := by sorry

/- HOL4: Theorem tenv_ctor_ok_lookup -/
theorem tenv_ctor_ok_lookup : True := by sorry

/- HOL4: Theorem bind_tvar_rewrites[simp] -/
theorem bind_tvar_rewrites : True := by sorry

/- HOL4: Theorem bind_tvar0[simp] -/
theorem bind_tvar0 : True := by sorry

/- HOL4: Theorem tveLookup_subst_none -/
theorem tveLookup_subst_none : True := by sorry

/- HOL4: Theorem tveLookup_db_merge_none -/
theorem tveLookup_db_merge_none : True := by sorry

/- HOL4: Theorem tveLookup_inc_none -/
theorem tveLookup_inc_none : True := by sorry

/- HOL4: Theorem tveLookup_freevars -/
theorem tveLookup_freevars_thm : True := by sorry

/- HOL4: Theorem bind_var_list_append -/
theorem bind_var_list_append : True := by sorry

/- HOL4: Theorem num_tvs_bind_var_list[simp] -/
theorem num_tvs_bind_var_list : True := by sorry

/- HOL4: Theorem tenv_val_exp_ok_bvl -/
theorem tenv_val_exp_ok_bvl : True := by sorry

/- HOL4: Theorem tveLookup_subst_some -/
theorem tveLookup_subst_some : True := by sorry

/- HOL4: Theorem num_tvs_db_merge[simp] -/
theorem num_tvs_db_merge : True := by sorry

/- HOL4: Theorem num_tvs_deBruijn_subst_tenvE[simp] -/
theorem num_tvs_deBruijn_subst_tenvE : True := by sorry

/- HOL4: Theorem tveLookup_inc_some -/
theorem tveLookup_inc_some : True := by sorry

/- HOL4: Theorem tveLookup_freevars_subst -/
theorem tveLookup_freevars_subst : True := by sorry

/- HOL4: Theorem tenv_val_exp_ok_db_merge -/
theorem tenv_val_exp_ok_db_merge : True := by sorry

/- HOL4: Theorem tveLookup_no_tvs -/
theorem tveLookup_no_tvs : True := by sorry

/- HOL4: Theorem deBruijn_subst_E_bvl -/
theorem deBruijn_subst_E_bvl : True := by sorry

/- HOL4: Theorem db_merge_bvl -/
theorem db_merge_bvl : True := by sorry

/- HOL4: Theorem tveLookup_db_merge_some -/
theorem tveLookup_db_merge_some : True := by sorry

/- HOL4: Theorem type_op_cases -/
theorem type_op_cases_thm : True := by sorry

/- HOL4: Theorem type_ps_length -/
theorem type_ps_length : True := by sorry

/- HOL4: Theorem type_p_freevars -/
theorem type_p_freevars : True := by sorry

/- HOL4: Theorem type_p_subst -/
theorem type_p_subst : True := by sorry

/- HOL4: Theorem type_p_bvl -/
theorem type_p_bvl : True := by sorry

/- HOL4: Theorem type_p_tenvV_indep -/
theorem type_p_tenvV_indep : True := by sorry

/- HOL4: Theorem type_es_list_rel -/
theorem type_es_list_rel : True := by sorry

/- HOL4: Theorem type_es_length -/
theorem type_es_length : True := by sorry

/- HOL4: Theorem tenv_val_exp_ok_bvl_funs -/
theorem tenv_val_exp_ok_bvl_funs : True := by sorry

/- HOL4: Theorem type_e_freevars -/
theorem type_e_freevars : True := by sorry

/- HOL4: Theorem type_e_subst -/
theorem type_e_subst : True := by sorry

/- HOL4: Theorem type_funs_Tfn -/
theorem type_funs_Tfn : True := by sorry

/- HOL4: Theorem type_funs_lookup -/
theorem type_funs_lookup : True := by sorry

/- HOL4: Theorem type_funs_find_recfun -/
theorem type_funs_find_recfun : True := by sorry

/- HOL4: Theorem type_recfun_lookup -/
theorem type_recfun_lookup : True := by sorry

/- HOL4: Theorem type_funs_distinct -/
theorem type_funs_distinct : True := by sorry

/- HOL4: Theorem mem_type_def_to_ctMap -/
theorem mem_type_def_to_ctMap : True := by sorry

/- HOL4: Theorem ctMap_ok_merge_imp -/
theorem ctMap_ok_merge_imp : True := by sorry

/- HOL4: Theorem ctMap_ok_lookup -/
theorem ctMap_ok_lookup : True := by sorry

/- HOL4: Theorem type_def_to_ctMap_mem -/
theorem type_def_to_ctMap_mem : True := by sorry

/- HOL4: Theorem ctMap_ok_type_defs -/
theorem ctMap_ok_type_defs : True := by sorry

/- HOL4: Theorem nsLookup_add_tenvE1 -/
theorem nsLookup_add_tenvE1 : True := by sorry

/- HOL4: Theorem nsLookup_add_tenvE2 -/
theorem nsLookup_add_tenvE2 : True := by sorry

/- HOL4: Theorem nsLookup_add_tenvE3 -/
theorem nsLookup_add_tenvE3 : True := by sorry

/- HOL4: Theorem add_tenvE_bvl -/
theorem add_tenvE_bvl : True := by sorry

/- HOL4: Theorem type_v_freevars -/
theorem type_v_freevars : True := by sorry

/- HOL4: Theorem type_subst_thm -/
theorem type_subst_thm : True := by sorry

/- HOL4: Theorem check_ctor_tenv_ok -/
theorem check_ctor_tenv_ok : True := by sorry

/- HOL4: Theorem type_d_check_uniq -/
theorem type_d_check_uniq : True := by sorry

/- HOL4: Theorem extend_dec_tenv_ok -/
theorem extend_dec_tenv_ok : True := by sorry

/- HOL4: Theorem type_d_tenv_ok_helper -/
theorem type_d_tenv_ok_helper : True := by sorry

/- HOL4: Theorem type_d_tenv_ok -/
theorem type_d_tenv_ok : True := by sorry

/- HOL4: Theorem type_d_mod -/
theorem type_d_mod : True := by sorry

/- HOL4: Theorem type_ds_empty[simp] -/
theorem type_ds_empty : True := by sorry

/- HOL4: Theorem type_ds_sing[simp] -/
theorem type_ds_sing : True := by sorry

/- HOL4: Theorem type_ds_mod -/
theorem type_ds_mod : True := by sorry

/- HOL4: Theorem type_specs_no_mod -/
theorem type_specs_no_mod : True := by sorry

/- HOL4: Theorem type_prog_empty[simp] -/
theorem type_prog_empty : True := by sorry

/- HOL4: Theorem type_prog_sing[simp] -/
theorem type_prog_sing : True := by sorry

/- HOL4: Theorem lookup_tenv_names -/
theorem lookup_tenv_names : True := by sorry

/- HOL4: Theorem tenv_names_bind_var_list -/
theorem tenv_names_bind_var_list : True := by sorry

/- HOL4: Theorem tenv_names_bind_var_list2 -/
theorem tenv_names_bind_var_list2 : True := by sorry
