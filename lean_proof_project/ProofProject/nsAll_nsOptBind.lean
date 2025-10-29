-- LEAN 4 file for theorem: nsAll_nsOptBind
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll_nsOptBind : ∀ {α β : Type} (P : α → β → Prop) (x : Option α) (v : β) (e : List (α × β)),
  ((x = none ∨ (∃ n : α, x = some n ∧ P (Short n) v)) ∧ nsAll P e) → nsAll P (nsOptBind x v e) := by
  aesop
