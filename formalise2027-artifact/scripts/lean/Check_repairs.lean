import LeanTypeSound
open HOL4

/-! Run on the repaired translation (snapshot 4841f993e). Proofs of the two frozen
    statements that were refutable before the repair.
    The statements are copied from the repaired translation. -/

-- explode_aux_thm, with strsub indexing characters as HOL4 `EL n s` does.
theorem explode_aux_thm_holds (max n : Nat) (ls : String) :
    n + max = ls.toList.length →
    explode_aux (.strlit ls) n max = HOL4.DROP n ls.toList := by
  induction max generalizing n with
  | zero =>
    intro h
    simp only [explode_aux, HOL4.DROP]
    rw [List.drop_eq_nil_of_le (by omega)]
  | succ k ih =>
    intro h
    have hn : n < ls.toList.length := by omega
    rw [explode_aux, ih (n + 1) (by omega)]
    simp only [HOL4.DROP, strsub]
    rw [List.drop_eq_getElem_cons hn, getElem!_pos ls.toList n hn]

theorem explode_thm_holds (ls : String) : explode (.strlit ls) = ls.toList := by
  have := explode_aux_thm_holds (strlen (.strlit ls)) 0 ls (by simp [strlen, String.length_toList])
  simpa [explode, HOL4.DROP] using this

-- nsLookup_nsBind, with lawful equality on module and name keys.
theorem nsLookup_nsBind_holds {m n v : Type} [BEq m] [LawfulBEq m] [BEq n] [LawfulBEq n] :
    (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
      nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
    (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
      id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_) := by
  constructor
  · intro n_ val_ e
    cases e
    simp [nsBind, nsLookup, ALOOKUP]
  · intro id_ n_ val_ e hne
    cases e with
    | Bind vals mods =>
      cases id_ with
      | Short x =>
        have hx : (n_ == x) = false := by
          simp only [beq_eq_false_iff_ne]; intro h; exact hne (by rw [h])
        simp [nsBind, nsLookup, ALOOKUP, hx]
      | Long mn i => simp [nsBind, nsLookup]


/-! Definition repairs checked against the HOL4 meaning. -/

-- HOL4 `FV (Letrec defs b) = FV_defs defs ∪ FV b DIFF ...` groups to the left, so a
-- recursive call to `f` inside its own body is bound.
theorem FV_Letrec_binds_recursive_call :
    ¬ (FV (.Letrec [(.strlit "f", .strlit "x", .Var (.Short (.strlit "f")))]
        (.Var (.Short (.strlit "g"))))) (cml_id.Short (.strlit "f")) := by
  simp [FV, FV_defs, SDiff.sdiff, Set.sdiff, Union.union, Set.union, Set.insert]

-- HOL4 `FEMPTY |++ REVERSE l` equals `alist_to_fmap l`, in which the first binding wins.
theorem FUPDATE_LIST_reverse {α β : Type} [BEq α] (l : List (α × β)) :
    Finmap.FUPDATE_LIST Finmap.FEMPTY l.reverse = Finmap.alist_to_fmap l := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    funext k
    simp only [Finmap.FUPDATE_LIST, List.reverse_cons, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at ih ⊢
    rw [ih]
    simp only [Finmap.FUPDATE, Finmap.alist_to_fmap, List.find?_cons]
    cases k == p.1 <;> simp

-- strsub also feeds isSubstring and tokens. HOL4 isSubstring "a" "éa" holds.
theorem isSubstring_multibyte : isSubstring (.strlit "a") (.strlit "éa") = true := by decide

-- The repaired theorem statements have the same types as the proved ones above.
example : type_of% @explode_thm = type_of% @explode_thm_holds := rfl
example : type_of% @nsLookup_nsBind = type_of% @nsLookup_nsBind_holds := rfl

#print axioms explode_thm_holds
#print axioms nsLookup_nsBind_holds
#print axioms FV_Letrec_binds_recursive_call
#print axioms FUPDATE_LIST_reverse
#print axioms isSubstring_multibyte
