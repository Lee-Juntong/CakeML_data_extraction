import LeanTypeSound
-- An unlawful equality on keys: nothing is equal to itself.
@[reducible] def badBEq : BEq Unit := ⟨fun _ _ => false⟩

-- The frozen statement of nsLookup_nsBind (sorry-admitted in the baseline)
-- is false: its type is refutable by instantiating the key equality with badBEq.
theorem nsLookup_nsBind_statement_false :
    ¬ (∀ {m n v : Type} [BEq m] [BEq n],
      (∀ (n_ : n) (val_ : v) (e : «namespace» m n v),
        nsLookup (nsBind n_ val_ e) (cml_id.Short n_) = some val_) ∧
      (∀ (id_ : cml_id m n) (n_ : n) (val_ : v) (e : «namespace» m n v),
        id_ ≠ cml_id.Short n_ → nsLookup (nsBind n_ val_ e) id_ = nsLookup e id_)) := by
  intro h
  have := (@h Unit Unit Unit instBEqOfDecidableEq badBEq).1 () () (.Bind [] [])
  revert this
  decide

-- The two types agree syntactically, so the admitted theorem proves False.
example : False := nsLookup_nsBind_statement_false nsLookup_nsBind
#print axioms nsLookup_nsBind_statement_false
