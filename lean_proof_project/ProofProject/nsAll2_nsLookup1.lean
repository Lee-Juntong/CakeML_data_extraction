-- LEAN 4 file for theorem: nsAll2_nsLookup1
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_nsLookup1 : ∀ (α β : Type) (R : α → β → β → Prop) (e1 e2 : List (α × β)) (n : α) (v1 : β), nsLookup e1 n = some v1 ∧ nsAll2 R e1 e2 → ∃ (v2 : β), nsLookup e2 n = some v2 ∧ R n v1 v2 := by
  aesop
