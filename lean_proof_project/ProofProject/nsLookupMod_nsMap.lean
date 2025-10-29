-- LEAN 4 file for theorem: nsLookupMod_nsMap
-- Original HOL4 Theorem

import Mathlib.Tactic
import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

-- Theorem with auto-prover
theorem nsLookupMod_nsMap : ∀ {α β : Type} [Functor Ns] (n : Ns α) (x : Key) (f : α → β), nsLookupMod (nsMap f n) x = Option.map (nsMap f) (nsLookupMod n x) := by
  aesop
