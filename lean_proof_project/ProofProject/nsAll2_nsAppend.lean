-- LEAN 4 file for theorem: nsAll2_nsAppend
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll2_nsAppend : ∀ {α β : Type} (R : α → β → Prop) (e1 e1' : List α) (e2 e2' : List β), nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' → nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  aesop
