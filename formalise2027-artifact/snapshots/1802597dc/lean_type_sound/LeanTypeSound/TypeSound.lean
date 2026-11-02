/-
  Translation of typeSoundScript.sml
  Proof of type soundness: a type-correct program does not crash.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.TypeSystem
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.FpSem
import LeanTypeSound.Evaluate
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitivesProps
import LeanTypeSound.EvaluateProps
import LeanTypeSound.Weakening
import LeanTypeSound.TypeSysProps
import LeanTypeSound.TypeSoundInvariants
import LeanTypeSound.SemanticsMin

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition store_type_extension_def:
  store_type_extension tenvS1 tenvS2 =
  ?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) ∧
           (!l. (FLOOKUP tenvS' l = NONE) ∨ (FLOOKUP tenvS1 l = NONE))
End
-/
def store_type_extension (tenvS1 tenvS2 : tenv_store) : Prop :=
  ∃ tenvS',
    tenvS2 = Finmap.FUNION tenvS' tenvS1 ∧
    (∀ l, Finmap.FLOOKUP tenvS' l = none ∨ Finmap.FLOOKUP tenvS1 l = none)

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem v_unchanged[simp] -/
theorem v_unchanged : True := by sorry

/- HOL4: Theorem check_dup_ctors_thm -/
theorem check_dup_ctors_thm : True := by sorry

/- HOL4: Theorem prim_canonical_values_thm -/
theorem prim_canonical_values_thm : True := by sorry

/- HOL4: Theorem ctor_canonical_values_thm -/
theorem ctor_canonical_values_thm : True := by sorry

/- HOL4: Theorem opapp_type_sound -/
theorem opapp_type_sound : True := by sorry

/- HOL4: Theorem store_type_extension_weakS -/
theorem store_type_extension_weakS : True := by sorry

/- HOL4: Theorem store_type_extension_refl -/
theorem store_type_extension_refl : True := by sorry

/- HOL4: Theorem store_type_extension_trans -/
theorem store_type_extension_trans : True := by sorry

/- HOL4: Theorem store_assign_type_sound -/
theorem store_assign_type_sound : True := by sorry

/- HOL4: Theorem store_alloc_type_sound -/
theorem store_alloc_type_sound : True := by sorry

/- HOL4: Theorem store_lookup_type_sound -/
theorem store_lookup_type_sound : True := by sorry

/- HOL4: Theorem type_v_list_to_v -/
theorem type_v_list_to_v : True := by sorry

/- HOL4: Theorem type_v_list_to_v_APPEND -/
theorem type_v_list_to_v_APPEND : True := by sorry

/- HOL4: Theorem do_eq_Boolv -/
theorem do_eq_Boolv : True := by sorry

/- HOL4: Theorem prim_canonical_Boolv_thm -/
theorem prim_canonical_Boolv_thm : True := by sorry

/- HOL4: Theorem op_type_sound -/
theorem op_type_sound : True := by sorry

/- HOL4: Theorem build_conv_type_sound -/
theorem build_conv_type_sound : True := by sorry

/- HOL4: Theorem same_ctor_and_same_tid -/
theorem same_ctor_and_same_tid : True := by sorry

/- HOL4: Theorem pat_type_sound -/
theorem pat_type_sound : True := by sorry

/- HOL4: Theorem lookup_var_sound -/
theorem lookup_var_sound : True := by sorry

/- HOL4: Theorem EVERY_REPLICATE -/
theorem EVERY_REPLICATE : True := by sorry

/- HOL4: Theorem EVERY_LIST_REL -/
theorem EVERY_LIST_REL_thm : True := by sorry

/- HOL4: Theorem exp_type_sound -/
theorem exp_type_sound : True := by sorry

/- HOL4: Theorem type_all_env_extend -/
theorem type_all_env_extend : True := by sorry

/- HOL4: Theorem type_e_con_check -/
theorem type_e_con_check : True := by sorry

/- HOL4: Theorem decs_type_sound_no_check -/
theorem decs_type_sound_no_check : True := by sorry

/- HOL4: Theorem decs_type_sound -/
theorem decs_type_sound : True := by sorry

/- HOL4: Theorem semantics_type_sound -/
theorem semantics_type_sound : True := by sorry
