-- LEAN 4 file for theorem: nsLookup_alist_to_ns_none
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_alist_to_ns_none : ∀ {α : Type} (l : List (String × α)) (id : Name),
  nsLookup (alist_to_ns l) id = none
  ↔
  ∀ (x' : String), id = Name.short x' → ALOOKUP l x' = none := by
  aesop
