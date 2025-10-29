-- LEAN 4 file for theorem: nsLookup_alist_to_ns_some
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_alist_to_ns_some : nsLookup_alist_to_ns_some {α : Type} (l : List (String × α)) (id : NamespaceId) (v : α) :
  nsLookup (alist_to_ns l) id = some v ↔ ∃ x' : String, id = NamespaceId.short x' ∧ ALOOKUP l x' = some v := by
  aesop
