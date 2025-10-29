-- LEAN 4 file for theorem: nsAll_nsAppend_left
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAll_nsAppend_left : ∀ (α : Type) (P : α → Prop) (n1 n2 : List α), (∀ x ∈ (n1 ++ n2), P x) → (∀ x ∈ n1, P x) := by
  aesop
