-- LEAN 4 file for theorem: nsAll_nsAppend
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll_nsAppend : ∀ (α : Type) (f : α → Prop) (e1 e2 : List α), nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  aesop
