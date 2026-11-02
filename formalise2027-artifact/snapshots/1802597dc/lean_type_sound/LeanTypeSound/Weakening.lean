/-
  Translation of weakeningScript.sml
  Weakening lemmas used in type soundness.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.TypeSystem
import LeanTypeSound.TypeSysProps
import LeanTypeSound.NamespaceProps
import LeanTypeSound.SemanticPrimitives
import LeanTypeSound.TypeSoundInvariants

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition weak_tenvE_def:
weak_tenvE tenv tenv' =
  (num_tvs tenv ≥ num_tvs tenv' ∧
   ∀n inc tvs t.
    (tveLookup n inc tenv' = SOME (tvs,t)) ⇔
    (tveLookup n inc tenv = SOME (tvs,t)))
End
-/
def weak_tenvE (tenvE tenvE' : tenv_val_exp) : Prop :=
  num_tvs tenvE ≥ num_tvs tenvE' ∧
  ∀ n inc tvs t,
    (tveLookup n inc tenvE' = some (tvs, t)) ↔
    (tveLookup n inc tenvE = some (tvs, t))

/- HOL4:
Definition weakS_def:
weakS tenvS tenvS' ⇔ tenvS' SUBMAP tenvS
End
-/
def weakS (tenvS tenvS' : tenv_store) : Prop :=
  Finmap.SUBMAP tenvS' tenvS

/- HOL4:
Definition weak_def:
weak tenv' tenv ⇔
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv
End
-/
def weak (tenv' tenv : type_env) : Prop :=
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv

/- HOL4:
Definition weakCT_def:
weakCT cenv_impl cenv_spec ⇔ cenv_spec SUBMAP cenv_impl
End
-/
def weakCT (cenv_impl cenv_spec : ctMap) : Prop :=
  Finmap.SUBMAP cenv_spec cenv_impl

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem weak_tenv_refl -/
theorem weak_tenv_refl : True := by sorry

/- HOL4: Theorem weakS_refl -/
theorem weakS_refl : True := by sorry

/- HOL4: Theorem type_p_weakening -/
theorem type_p_weakening : True := by sorry

/- HOL4: Theorem type_e_weakening -/
theorem type_e_weakening : True := by sorry

/- HOL4: Theorem weakCT_refl -/
theorem weakCT_refl : True := by sorry

/- HOL4: Theorem weakCT_trans -/
theorem weakCT_trans : True := by sorry

/- HOL4: Theorem disjoint_env_weakCT -/
theorem disjoint_env_weakCT : True := by sorry

/- HOL4: Theorem type_tenv_ctor_weakening -/
theorem type_tenv_ctor_weakening : True := by sorry

/- HOL4: Theorem type_v_weakening -/
theorem type_v_weakening : True := by sorry

/- HOL4: Theorem type_all_env_weakening -/
theorem type_all_env_weakening : True := by sorry

/- HOL4: Theorem type_sv_weakening -/
theorem type_sv_weakening : True := by sorry

/- HOL4: Theorem type_s_weakening -/
theorem type_s_weakening : True := by sorry

/- HOL4: Theorem weak_tenv_extend_dec_tenv -/
theorem weak_tenv_extend_dec_tenv : True := by sorry
