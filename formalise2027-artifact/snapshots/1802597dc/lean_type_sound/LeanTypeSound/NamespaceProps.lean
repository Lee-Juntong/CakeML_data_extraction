/-
  Translation of namespacePropsScript.sml
  Proofs about the namespace datatype.
-/
import LeanTypeSound.HOL4Prelude
import LeanTypeSound.Ast
import LeanTypeSound.Namespace

open HOL4

-- ============================================================
-- Definitions
-- ============================================================

/- HOL4:
Definition alist_rel_restr_def:
  (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
End
-/
def alist_rel_restr {k v1 v2 : Type} [BEq k]
    (R : k → v1 → v2 → Prop) (l1 : List (k × v1)) (l2 : List (k × v2)) :
    List k → Prop
  | [] => True
  | k1 :: keys =>
    match ALOOKUP l1 k1 with
    | none => False
    | some val1 =>
      match ALOOKUP l2 k1 with
      | none => False
      | some val2 => R k1 val1 val2 ∧ alist_rel_restr R l1 l2 keys

/- HOL4:
Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End
-/
def alistSub {k v1 v2 : Type} [BEq k]
    (R : k → v1 → v2 → Prop) (e1 : List (k × v1)) (e2 : List (k × v2)) : Prop :=
  alist_rel_restr R e1 e2 (e1.map Prod.fst)

/- HOL4:
Definition nsSub_compute_def:
  nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (λk v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (λk v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
End
-/
def nsSub_compute {m n v1 v2 : Type} [BEq m] [BEq n]
    (path : List m) (R : cml_id m n → v1 → v2 → Prop) :
    «namespace» m n v1 → «namespace» m n v2 → Prop
  | .Bind e1V e1M, .Bind e2V e2M =>
    alistSub (fun k val1 val2 => R (mk_id path.reverse k) val1 val2) e1V e2V ∧
    alistSub (fun k val1 val2 => nsSub_compute (k :: path) R val1 val2) e1M e2M
  decreasing_by all_goals sorry

-- ============================================================
-- Theorem stubs
-- ============================================================

/- HOL4: Theorem mk_id_surj: !id. ?p n. id = mk_id p n -/
theorem mk_id_surj : True := by sorry

/- HOL4: Theorem mk_id_thm: !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm : True := by sorry

/- HOL4: Theorem nsSub_mono[mono] -/
theorem nsSub_mono : True := by sorry

/- HOL4: Theorem nsAll2_mono[mono] -/
theorem nsAll2_mono : True := by sorry

/- HOL4: Theorem nsLookup_nsEmpty[simp] -/
theorem nsLookup_nsEmpty : True := by sorry

/- HOL4: Theorem nsLookupMod_nsEmpty[simp] -/
theorem nsLookupMod_nsEmpty : True := by sorry

/- HOL4: Theorem nsAppend_nsEmpty[simp] -/
theorem nsAppend_nsEmpty : True := by sorry

/- HOL4: Theorem alist_to_ns_nil[simp] -/
theorem alist_to_ns_nil : True := by sorry

/- HOL4: Theorem nsSub_nsEmpty[simp] -/
theorem nsSub_nsEmpty : True := by sorry

/- HOL4: Theorem nsAll_nsEmpty[simp] -/
theorem nsAll_nsEmpty : True := by sorry

/- HOL4: Theorem nsAll2_nsEmpty[simp] -/
theorem nsAll2_nsEmpty : True := by sorry

/- HOL4: Theorem alist_to_ns_cons[simp] -/
theorem alist_to_ns_cons : True := by sorry

/- HOL4: Theorem nsAppend_nsBind[simp] -/
theorem nsAppend_nsBind : True := by sorry

/- HOL4: Theorem nsAppend_assoc[simp] -/
theorem nsAppend_assoc : True := by sorry

/- HOL4: Theorem nsLookup_nsBind[simp] -/
theorem nsLookup_nsBind : True := by sorry

/- HOL4: Theorem nsAppend_nsSing[simp] -/
theorem nsAppend_nsSing : True := by sorry

/- HOL4: Theorem nsLookup_nsSing[simp] -/
theorem nsLookup_nsSing : True := by sorry

/- HOL4: Theorem nsAll_nsSing[simp] -/
theorem nsAll_nsSing : True := by sorry

/- HOL4: Theorem nsAll2_nsSing[simp] -/
theorem nsAll2_nsSing : True := by sorry

/- HOL4: Theorem nsBind_11[simp] -/
theorem nsBind_11 : True := by sorry

/- HOL4: Theorem alist_to_ns_11[simp] -/
theorem alist_to_ns_11 : True := by sorry

/- HOL4: Theorem nsLookup_nsLift -/
theorem nsLookup_nsLift : True := by sorry

/- HOL4: Theorem nsLookupMod_nsLift -/
theorem nsLookupMod_nsLift : True := by sorry

/- HOL4: Theorem nsLookup_nsAppend_some -/
theorem nsLookup_nsAppend_some : True := by sorry

/- HOL4: Theorem nsAppend_to_nsBindList -/
theorem nsAppend_to_nsBindList : True := by sorry

/- HOL4: Theorem nsLookupMod_nsAppend_none -/
theorem nsLookupMod_nsAppend_none : True := by sorry

/- HOL4: Theorem eALL_T[simp] -/
theorem eALL_T : True := by sorry

/- HOL4: Theorem nsLookup_nsAll -/
theorem nsLookup_nsAll : True := by sorry

/- HOL4: Theorem nsAll_nsAppend -/
theorem nsAll_nsAppend : True := by sorry

/- HOL4: Theorem nsAll_alist_to_ns -/
theorem nsAll_alist_to_ns : True := by sorry

/- HOL4: Theorem nsAll_nsLift[simp] -/
theorem nsAll_nsLift : True := by sorry

/- HOL4: Theorem nsAll_nsAppend_left -/
theorem nsAll_nsAppend_left : True := by sorry

/- HOL4: Theorem nsSub_conj -/
theorem nsSub_conj : True := by sorry

/- HOL4: Theorem nsSub_refl -/
theorem nsSub_refl : True := by sorry

/- HOL4: Theorem nsSub_nsBind -/
theorem nsSub_nsBind : True := by sorry

/- HOL4: Theorem nsSub_nsAppend2 -/
theorem nsSub_nsAppend2 : True := by sorry

/- HOL4: Theorem alist_rel_restr_thm -/
theorem alist_rel_restr_thm : True := by sorry

/- HOL4: Theorem alistSub_cong -/
theorem alistSub_cong : True := by sorry

/- HOL4: Theorem nsLookup_FOLDR_nsLift -/
theorem nsLookup_FOLDR_nsLift : True := by sorry

/- HOL4: Theorem nsLookup_FOLDR_nsLift_some -/
theorem nsLookup_FOLDR_nsLift_some : True := by sorry

/- HOL4: Theorem nsLookupMod_FOLDR_nsLift_none -/
theorem nsLookupMod_FOLDR_nsLift_none : True := by sorry

/- HOL4: Theorem nsAll2_conj -/
theorem nsAll2_conj : True := by sorry

/- HOL4: Theorem nsAll2_nsLookup2 -/
theorem nsAll2_nsLookup2 : True := by sorry

/- HOL4: Theorem nsAll2_nsLookup_none -/
theorem nsAll2_nsLookup_none : True := by sorry

/- HOL4: Theorem nsAll2_nsBind -/
theorem nsAll2_nsBind : True := by sorry

/- HOL4: Theorem nsAll2_nsBindList -/
theorem nsAll2_nsBindList : True := by sorry

/- HOL4: Theorem nsAll2_nsAppend -/
theorem nsAll2_nsAppend : True := by sorry

/- HOL4: Theorem nsAll2_alist_to_ns -/
theorem nsAll2_alist_to_ns : True := by sorry

/- HOL4: Theorem nsAll2_nsLift[simp] -/
theorem nsAll2_nsLift : True := by sorry
