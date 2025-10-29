-- LEAN 4 file for theorem: nsAppend_to_nsBindList
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsAppend_to_nsBindList : ∀ {α β : Type} (l : List (α × β)) (e : α × β), nsAppend (alist_to_ns l) e = nsBindList l e := by
  aesop
