import LeanTypeSound

-- strsub indexes the Lean string by byte position, while HOL4 strsub indexes characters.
-- For a string with a multi-byte character, explode no longer returns the characters.
theorem explode_thm_statement_false :
    ¬ (∀ (ls : String), explode (.strlit ls) = ls.data) := by
  intro h
  have := h "éa"
  revert this
  decide

#print axioms explode_thm_statement_false
