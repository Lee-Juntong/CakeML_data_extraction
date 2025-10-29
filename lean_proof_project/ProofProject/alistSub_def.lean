-- LEAN 4 file for theorem: alistSub_def
-- Original HOL4 Definition

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem alistSub_def : def alistSub {α β : Type} (R : (α × β) → Prop) (e1 e2 : List (α × β)) : Prop := alist_rel_restr R e1 e2 (List.map Prod.fst e1) := by
  aesop
