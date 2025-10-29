-- LEAN 4 file for theorem: nsMap_nsAppend
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsMap_nsAppend : ∀ (α β : Type) (f : α → β) (n1 n2 : List α), List.map f (n1 ++ n2) = (List.map f n1) ++ (List.map f n2) := by
  aesop
