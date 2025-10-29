-- LEAN 4 file for theorem: nsLookup_nsAll
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_nsAll : ∀ {α β : Type} (env : List (α × β)) (x : α) (P : α → β → Prop) (v : β), nsAll P env ∧ nsLookup env x = some v → P x v := by
  aesop
