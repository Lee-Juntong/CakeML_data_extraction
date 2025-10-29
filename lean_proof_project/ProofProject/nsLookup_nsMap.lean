-- LEAN 4 file for theorem: nsLookup_nsMap
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookup_nsMap : ∀ {α β : Type} (n : NameServerMap α) (x : Name) (f : α → β), nsLookup (nsMap f n) x = Option.map f (nsLookup n x) := by
  aesop
