/-
  Translation of semanticPrimitivesPropsScript.sml
  Various basic properties of the semantic primitives.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace
import LeanTypeSound.Ffi
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.NamespaceProps

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition map_error_result_def[simp]:
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f (Rabort a) = Rabort a)
End
-/
def map_error_result {α β : Type} (f : α → β) : error_result α → error_result β
  | .Rraise e => .Rraise (f e)
  | .Rabort a => .Rabort a

/- HOL4:
Definition map_result_def[simp]:
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))
End
-/
def map_result {α β γ δ : Type} (f1 : α → β) (f2 : γ → δ) :
    result α γ → result β δ
  | .Rval v => .Rval (f1 v)
  | .Rerr e => .Rerr (map_error_result f2 e)

/- HOL4:
Definition every_error_result_def[simp]:
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P (Rabort a) = T)
End
-/
def every_error_result {α : Type} (P : α → Bool) : error_result α → Bool
  | .Rraise e => P e
  | .Rabort _ => true

/- HOL4:
Definition every_result_def[simp]:
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))
End
-/
def every_result {α β : Type} (P1 : α → Bool) (P2 : β → Bool) : result α β → Bool
  | .Rval v => P1 v
  | .Rerr e => every_error_result P2 e

/- HOL4:
Definition map_sv_def[simp]:
  map_sv f (Refv v) = Refv (f v) ∧
  map_sv _ (W8array w) = (W8array w) ∧
  map_sv f (Varray vs) = (Varray (MAP f vs)) ∧
  map_sv f (Thunk m v) = (Thunk m (f v))
End
-/
def map_sv {α β : Type} (f : α → β) : store_v α → store_v β
  | .Refv v => .Refv (f v)
  | .W8array w => .W8array w
  | .Varray vs => .Varray (vs.map f)
  | .Thunk m v => .Thunk m (f v)

/- HOL4:
Definition dest_Refv_def[simp]:
  dest_Refv (Refv v) = v
End
-/
def dest_Refv {α : Type} [Inhabited α] : store_v α → α
  | .Refv v => v
  | _ => default

/- HOL4:
Definition store_v_vs_def[simp]:
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = [] ∧
  store_v_vs (Thunk _ v) = [v]
End
-/
def store_v_vs {α : Type} : store_v α → List α
  | .Refv v => [v]
  | .Varray vs => vs
  | .W8array _ => []
  | .Thunk _ v => [v]

/- HOL4:
Definition ctors_of_tdef_def[simp]:
  ctors_of_tdef (_,_,condefs) = MAP FST condefs
End
-/
def ctors_of_tdef : List tvarN × typeN × List (conN × List ast_t) → List conN
  | (_, _, condefs) => condefs.map Prod.fst

/- HOL4:
Definition FV_def[simp]: ... End
  Free variables of expressions (set-valued).
-/
mutual
def FV : exp → Set (cml_id modN varN)
  | .Raise e => FV e
  | .Handle e pes => FV e ∪ FV_pes pes
  | .Lit _ => ∅
  | .Con _ ls => FV_list ls
  | .Var id => {id}
  | .Fun x e => FV e \ {cml_id.Short x}
  | .App _ es => FV_list es
  | .Log _ e1 e2 => FV e1 ∪ FV e2
  | .If e1 e2 e3 => FV e1 ∪ FV e2 ∪ FV e3
  | .Mat e pes => FV e ∪ FV_pes pes
  | .Let xo e b => FV e ∪ (FV b \ (match xo with | none => ∅ | some x => {cml_id.Short x}))
  | .Letrec defs b => (FV_defs defs ∪ FV b) \ (fun x => x ∈ defs.map (fun (f, _, _) => cml_id.Short f))
  | .Tannot e _ => FV e
  | .Lannot e _ => FV e

def FV_list : List exp → Set (cml_id modN varN)
  | [] => ∅
  | e :: es => FV e ∪ FV_list es

def FV_pes : List (pat × exp) → Set (cml_id modN varN)
  | [] => ∅
  | (p, e) :: pes =>
    (FV e \ (Set.image cml_id.Short (fun x => x ∈ pat_bindings p []))) ∪ FV_pes pes

def FV_defs : List (varN × varN × exp) → Set (cml_id modN varN)
  | [] => ∅
  | (_, x, e) :: defs => (FV e \ {cml_id.Short x}) ∪ FV_defs defs
end

/- HOL4:
Definition FV_dec_def[simp]: ... End
-/
def FV_dec : dec → Set (cml_id modN varN)
  | .Dlet _ p e => FV (.Mat e [(p, .Lit (.IntLit 0))])
  | .Dletrec _ defs => FV (.Letrec defs (.Lit (.IntLit 0)))
  | .Dtype _ _ => ∅
  | .Dtabbrev _ _ _ _ => ∅
  | .Dexn _ _ _ => ∅
  | .Dmod _ _ => ∅
  | .Dlocal _ _ => ∅
  | .Denv _ => ∅

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem with_same_v[simp] -/
theorem with_same_v : True := by sorry

/- HOL4: Theorem unchanged_env[simp] -/
theorem unchanged_env : True := by sorry

/- HOL4: Theorem with_same_clock -/
theorem with_same_clock : True := by sorry

/- HOL4: Theorem Boolv_11[simp] -/
theorem Boolv_11 : True := by sorry

/- HOL4: Theorem extend_dec_env_assoc[simp] -/
theorem extend_dec_env_assoc : True := by sorry

/- HOL4: Theorem pat_bindings_accum -/
theorem pat_bindings_accum : True := by sorry

/- HOL4: Theorem do_app_cases -/
theorem do_app_cases : True := by sorry

/- HOL4: Theorem build_rec_env_merge -/
theorem build_rec_env_merge : True := by sorry

/- HOL4: Theorem do_con_check_build_conv -/
theorem do_con_check_build_conv : True := by sorry

/- HOL4: Theorem FV_pes_MAP -/
theorem FV_pes_MAP : True := by sorry

/- HOL4: Theorem FV_defs_MAP -/
theorem FV_defs_MAP : True := by sorry

/- HOL4: Theorem concrete_v_list[simp] -/
theorem concrete_v_list_thm : True := by sorry

/- HOL4: Theorem prim_type_cases -/
theorem prim_type_cases : True := by sorry
