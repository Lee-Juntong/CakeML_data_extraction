-- LEAN 4 file for theorem: nsLookup_nsDom
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_nsDom : nsLookup_nsDom {α β N : Type} (nsLookup : N → α → Option β) (nsDom : N → Set α) (x : α) (n : N) : x ∈ nsDom n ↔ ∃ (v : β), nsLookup n x = some v := by
  aesop
